#[cfg(feature = "std")]
mod multi_threaded;
mod single_threaded;

use alloc::{vec, vec::Vec};
use bevy_platform::collections::HashMap;
use bevy_utils::prelude::DebugName;
use core::any::TypeId;

pub use self::single_threaded::SingleThreadedExecutor;

#[cfg(feature = "std")]
pub use self::multi_threaded::{MainThreadExecutor, MultiThreadedExecutor};

use fixedbitset::FixedBitSet;

use crate::{
    change_detection::{CheckChangeTicks, Tick},
    error::{BevyError, ErrorContext, Result},
    prelude::{IntoSystemSet, SystemSet},
    query::FilteredAccessSet,
    schedule::{
        graph::{
            index,
            Direction::{Incoming, Outgoing},
        },
        ConditionWithAccess, InternedSystemSet, ScheduleGraph, ScheduleGraphAnalysis, SystemKey,
        SystemSetKey, SystemTypeSet, SystemWithAccess,
    },
    system::{RunSystemError, System, SystemIn, SystemParamValidationError, SystemStateFlags},
    world::{unsafe_world_cell::UnsafeWorldCell, DeferredWorld, World},
};

/// Types that can run a [`ScheduleExecutable`] on a [`World`].
pub(super) trait ScheduleExecutor: Send + Sync {
    fn kind(&self) -> ExecutorKind;

    fn init(&mut self, graph: &ScheduleGraph, analysis: ScheduleGraphAnalysis);

    fn run(
        &mut self,
        world: &mut World,
        skip_systems: Option<&FixedBitSet>,
        error_handler: fn(BevyError, ErrorContext),
    );

    fn set_apply_final_deferred(&mut self, value: bool);

    fn check_change_ticks(&mut self, check: CheckChangeTicks);

    fn apply_deferred(&mut self, world: &mut World);
}

/// Specifies how a [`Schedule`](super::Schedule) will be run.
///
/// The default depends on the target platform:
///  - [`SingleThreaded`](ExecutorKind::SingleThreaded) on Wasm.
///  - [`MultiThreaded`](ExecutorKind::MultiThreaded) everywhere else.
#[derive(PartialEq, Eq, Default, Debug, Copy, Clone)]
pub enum ExecutorKind {
    /// Runs the schedule using a single thread.
    ///
    /// Useful if you're dealing with a single-threaded environment, saving your threads for
    /// other things, or just trying minimize overhead.
    #[cfg_attr(
        any(
            target_arch = "wasm32",
            not(feature = "std"),
            not(feature = "multi_threaded")
        ),
        default
    )]
    SingleThreaded,
    /// Runs the schedule using a thread pool. Non-conflicting systems can run in parallel.
    #[cfg(feature = "std")]
    #[cfg_attr(all(not(target_arch = "wasm32"), feature = "multi_threaded"), default)]
    MultiThreaded,
}

/// Holds systems and conditions of a [`Schedule`](super::Schedule) sorted in
/// topological order (along with dependency information for `multi_threaded`
/// execution).
///
/// Since the arrays are sorted in the same order, elements are referenced by
/// their index. [`FixedBitSet`] is used as a smaller, more efficient substitute
/// of `HashSet<usize>`.
#[derive(Default)]
pub struct ScheduleExecutable {
    /// List of system node ids.
    pub(super) system_ids: Vec<SystemKey>,
    /// Indexed by system node id.
    pub(super) systems: Vec<SystemWithAccess>,
    /// Indexed by system node id.
    pub(super) system_conditions: Vec<Vec<ConditionWithAccess>>,
    /// Indexed by system node id.
    /// Number of systems that the system immediately depends on.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    pub(super) system_dependencies: Vec<usize>,
    /// Indexed by system node id.
    /// List of systems that immediately depend on the system.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    pub(super) system_dependents: Vec<Vec<usize>>,
    /// Indexed by system node id.
    /// List of sets containing the system that have conditions
    pub(super) sets_with_conditions_of_systems: Vec<FixedBitSet>,
    /// List of system set node ids.
    pub(super) set_ids: Vec<SystemSetKey>,
    /// Indexed by system set node id.
    pub(super) set_conditions: Vec<Vec<ConditionWithAccess>>,
    /// Indexed by system set node id.
    /// List of systems that are in sets that have conditions.
    ///
    /// If a set doesn't run because of its conditions, this is used to skip all systems in it.
    pub(super) systems_in_sets_with_conditions: Vec<FixedBitSet>,
}

impl ScheduleExecutable {
    /// Builds an execution-optimized [`SystemSchedule`] from the current state
    /// of the graph and its analysis.
    pub fn compile(
        graph: &ScheduleGraph,
        ScheduleGraphAnalysis {
            flat_dependency,
            hierarchy_analysis,
            ..
        }: ScheduleGraphAnalysis,
    ) -> Self {
        let dg_system_ids = flat_dependency.get_toposort().unwrap().to_vec();
        let dg_system_idx_map = dg_system_ids
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, id)| (id, i))
            .collect::<HashMap<_, _>>();

        let hierarchy_toposort = graph.hierarchy().get_toposort().unwrap();
        let hg_systems = hierarchy_toposort
            .iter()
            .cloned()
            .enumerate()
            .filter_map(|(i, id)| Some((i, id.as_system()?)))
            .collect::<Vec<_>>();
        let (hg_set_with_conditions_idxs, hg_set_ids): (Vec<_>, Vec<_>) = hierarchy_toposort
            .iter()
            .cloned()
            .enumerate()
            .filter_map(|(i, id)| {
                // ignore system sets that have no conditions
                // ignore system type sets (already covered, they don't have conditions)
                let key = id.as_set()?;
                graph.system_sets.has_conditions(key).then_some((i, key))
            })
            .unzip();

        let sys_count = graph.systems.len();
        let set_with_conditions_count = hg_set_ids.len();
        let hg_node_count = graph.hierarchy().node_count();

        // get the number of dependencies and the immediate dependents of each system
        // (needed by multi_threaded executor to run systems in the correct order)
        let mut system_dependencies = Vec::with_capacity(sys_count);
        let mut system_dependents = Vec::with_capacity(sys_count);
        for &sys_key in &dg_system_ids {
            let num_dependencies = flat_dependency
                .neighbors_directed(sys_key, Incoming)
                .count();

            let dependents = flat_dependency
                .neighbors_directed(sys_key, Outgoing)
                .map(|dep_id| dg_system_idx_map[&dep_id])
                .collect::<Vec<_>>();

            system_dependencies.push(num_dependencies);
            system_dependents.push(dependents);
        }

        // get the rows and columns of the hierarchy graph's reachability matrix
        // (needed to we can evaluate conditions in the correct order)
        let mut systems_in_sets_with_conditions =
            vec![FixedBitSet::with_capacity(sys_count); set_with_conditions_count];
        for (i, &row) in hg_set_with_conditions_idxs.iter().enumerate() {
            let bitset = &mut systems_in_sets_with_conditions[i];
            for &(col, sys_key) in &hg_systems {
                let idx = dg_system_idx_map[&sys_key];
                let is_descendant = hierarchy_analysis.reachable()[index(row, col, hg_node_count)];
                bitset.set(idx, is_descendant);
            }
        }

        let mut sets_with_conditions_of_systems =
            vec![FixedBitSet::with_capacity(set_with_conditions_count); sys_count];
        for &(col, sys_key) in &hg_systems {
            let i = dg_system_idx_map[&sys_key];
            let bitset = &mut sets_with_conditions_of_systems[i];
            for (idx, &row) in hg_set_with_conditions_idxs
                .iter()
                .enumerate()
                .take_while(|&(_idx, &row)| row < col)
            {
                let is_ancestor = hierarchy_analysis.reachable()[index(row, col, hg_node_count)];
                bitset.set(idx, is_ancestor);
            }
        }

        let mut systems = Vec::with_capacity(sys_count);
        let mut system_conditions = Vec::with_capacity(sys_count);
        let mut set_conditions = Vec::with_capacity(set_with_conditions_count);

        // Copy systems into new schedule
        for &key in &dg_system_ids {
            let system = graph.systems.get(key).unwrap().clone();
            let conditions = graph.systems.get_conditions(key).unwrap().to_vec();
            systems.push(system);
            system_conditions.push(conditions);
        }

        // Copy system set conditions into new schedule
        for &key in &hg_set_ids {
            let conditions = graph.system_sets.get_conditions(key).unwrap().to_vec();
            set_conditions.push(conditions);
        }

        Self {
            systems,
            system_conditions,
            set_conditions,
            system_ids: dg_system_ids,
            set_ids: hg_set_ids,
            system_dependencies,
            system_dependents,
            sets_with_conditions_of_systems,
            systems_in_sets_with_conditions,
        }
    }

    /// Iterates the change ticks of all systems in the schedule and clamps any
    /// older than [`MAX_CHANGE_AGE`](crate::change_detection::MAX_CHANGE_AGE).
    /// This prevents overflow and thus prevents false positives.
    pub fn check_change_tick(&mut self, check: CheckChangeTicks) {
        for SystemWithAccess { system, .. } in &mut self.systems {
            let mut system = system.lock();
            if !system.is_apply_deferred() {
                system.check_change_tick(check);
            }
        }

        for conditions in &mut self.system_conditions {
            for ConditionWithAccess { condition, .. } in conditions {
                condition.lock().check_change_tick(check);
            }
        }

        for conditions in &mut self.set_conditions {
            for ConditionWithAccess { condition, .. } in conditions {
                condition.lock().check_change_tick(check);
            }
        }
    }

    /// Directly applies any accumulated [`Deferred`](crate::system::Deferred)
    /// system parameters (like [`Commands`](crate::prelude::Commands)) to the
    /// `world`.
    ///
    /// Like always, deferred system parameters are applied in the "topological
    /// sort order" of the schedule graph. As a result, buffers from one system
    /// are only guaranteed to be applied before those of other systems if there
    /// is an explicit system ordering between the two systems.
    ///
    /// This is used in rendering to extract data from the main world, storing
    /// the data in system buffers, before applying their buffers in a different
    /// world.
    pub fn apply_deferred(&mut self, world: &mut World) {
        for SystemWithAccess { system, .. } in &mut self.systems {
            system.lock().apply_deferred(world);
        }
    }
}

/// A special [`System`] that instructs the executor to call
/// [`System::apply_deferred`] on the systems that have run but not applied
/// their [`Deferred`] system parameters (like [`Commands`]) or other system buffers.
///
/// ## Scheduling
///
/// `ApplyDeferred` systems are scheduled *by default*
/// - later in the same schedule run (for example, if a system with `Commands` param
///   is scheduled in `Update`, all the changes will be visible in `PostUpdate`)
/// - between systems with dependencies if the dependency [has deferred buffers]
///   (if system `bar` directly or indirectly depends on `foo`, and `foo` uses
///   `Commands` param, changes to the world in `foo` will be visible in `bar`)
///
/// ## Notes
/// - This system (currently) does nothing if it's called manually or wrapped
///   inside a [`PipeSystem`].
/// - Modifying a [`Schedule`] may change the order buffers are applied.
///
/// [`System::apply_deferred`]: crate::system::System::apply_deferred
/// [`Deferred`]: crate::system::Deferred
/// [`Commands`]: crate::prelude::Commands
/// [has deferred buffers]: crate::system::System::has_deferred
/// [`PipeSystem`]: crate::system::PipeSystem
/// [`Schedule`]: super::Schedule
#[doc(alias = "apply_system_buffers")]
pub struct ApplyDeferred;

impl dyn System<In = (), Out = ()> {
    /// Returns `true` if the system is an instance of [`ApplyDeferred`].
    pub(crate) fn is_apply_deferred(&self) -> bool {
        self.type_id() == TypeId::of::<ApplyDeferred>()
    }
}

impl System for ApplyDeferred {
    type In = ();
    type Out = ();

    fn name(&self) -> DebugName {
        DebugName::borrowed("bevy_ecs::apply_deferred")
    }

    fn flags(&self) -> SystemStateFlags {
        // non-send , exclusive , no deferred
        SystemStateFlags::NON_SEND | SystemStateFlags::EXCLUSIVE
    }

    unsafe fn run_unsafe(
        &mut self,
        _input: SystemIn<'_, Self>,
        _world: UnsafeWorldCell,
    ) -> Result<Self::Out, RunSystemError> {
        // This system does nothing on its own. The executor will apply deferred
        // commands from other systems instead of running this system.
        Ok(())
    }

    #[cfg(feature = "hotpatching")]
    #[inline]
    fn refresh_hotpatch(&mut self) {}

    fn run(
        &mut self,
        _input: SystemIn<'_, Self>,
        _world: &mut World,
    ) -> Result<Self::Out, RunSystemError> {
        // This system does nothing on its own. The executor will apply deferred
        // commands from other systems instead of running this system.
        Ok(())
    }

    fn apply_deferred(&mut self, _world: &mut World) {}

    fn queue_deferred(&mut self, _world: DeferredWorld) {}

    unsafe fn validate_param_unsafe(
        &mut self,
        _world: UnsafeWorldCell,
    ) -> Result<(), SystemParamValidationError> {
        // This system is always valid to run because it doesn't do anything,
        // and only used as a marker for the executor.
        Ok(())
    }

    fn initialize(&mut self, _world: &mut World) -> FilteredAccessSet {
        FilteredAccessSet::new()
    }

    fn check_change_tick(&mut self, _check: CheckChangeTicks) {}

    fn default_system_sets(&self) -> Vec<InternedSystemSet> {
        vec![SystemTypeSet::<Self>::new().intern()]
    }

    fn get_last_run(&self) -> Tick {
        // This system is never run, so it has no last run tick.
        Tick::MAX
    }

    fn set_last_run(&mut self, _last_run: Tick) {}
}

impl IntoSystemSet<()> for ApplyDeferred {
    type Set = SystemTypeSet<Self>;

    fn into_system_set(self) -> Self::Set {
        SystemTypeSet::<Self>::new()
    }
}

/// These functions hide the bottom of the callstack from `RUST_BACKTRACE=1` (assuming the default panic handler is used).
///
/// The full callstack will still be visible with `RUST_BACKTRACE=full`.
/// They are specialized for `System::run` & co instead of being generic over closures because this avoids an
/// extra frame in the backtrace.
///
/// This is reliant on undocumented behavior in Rust's default panic handler, which checks the call stack for symbols
/// containing the string `__rust_begin_short_backtrace` in their mangled name.
mod __rust_begin_short_backtrace {
    use core::hint::black_box;

    use crate::{
        error::Result,
        system::{ReadOnlySystem, RunSystemError},
        world::World,
    };
    #[cfg(feature = "std")]
    use crate::{system::System, world::unsafe_world_cell::UnsafeWorldCell};

    /// # Safety
    /// See `System::run_unsafe`.
    // This is only used by `MultiThreadedExecutor`, and would be dead code without `std`.
    #[cfg(feature = "std")]
    #[inline(never)]
    pub(super) unsafe fn run_unsafe(
        system: &mut dyn System<In = (), Out = ()>,
        world: UnsafeWorldCell,
    ) -> Result<(), RunSystemError> {
        let result = system.run_unsafe((), world);
        // Call `black_box` to prevent this frame from being tail-call optimized away
        black_box(());
        result
    }

    /// # Safety
    /// See `ReadOnlySystem::run_unsafe`.
    // This is only used by `MultiThreadedExecutor`, and would be dead code without `std`.
    #[cfg(feature = "std")]
    #[inline(never)]
    pub(super) unsafe fn readonly_run_unsafe<O: 'static>(
        system: &mut dyn ReadOnlySystem<In = (), Out = O>,
        world: UnsafeWorldCell,
    ) -> Result<O, RunSystemError> {
        // Call `black_box` to prevent this frame from being tail-call optimized away
        black_box(system.run_unsafe((), world))
    }

    #[cfg(feature = "std")]
    #[inline(never)]
    pub(super) fn run(
        system: &mut dyn System<In = (), Out = ()>,
        world: &mut World,
    ) -> Result<(), RunSystemError> {
        let result = system.run((), world);
        // Call `black_box` to prevent this frame from being tail-call optimized away
        black_box(());
        result
    }

    #[inline(never)]
    pub(super) fn run_without_applying_deferred(
        system: &mut dyn System<In = (), Out = ()>,
        world: &mut World,
    ) -> Result<(), RunSystemError> {
        let result = system.run_without_applying_deferred((), world);
        // Call `black_box` to prevent this frame from being tail-call optimized away
        black_box(());
        result
    }

    #[inline(never)]
    pub(super) fn readonly_run<O: 'static>(
        system: &mut dyn ReadOnlySystem<In = (), Out = O>,
        world: &mut World,
    ) -> Result<O, RunSystemError> {
        // Call `black_box` to prevent this frame from being tail-call optimized away
        black_box(system.run((), world))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        prelude::{Component, In, IntoSystem, Resource, Schedule},
        schedule::ExecutorKind,
        system::{Populated, Res, ResMut, Single},
        world::World,
    };

    #[derive(Component)]
    struct TestComponent;

    const EXECUTORS: [ExecutorKind; 2] =
        [ExecutorKind::SingleThreaded, ExecutorKind::MultiThreaded];

    #[derive(Resource, Default)]
    struct TestState {
        populated_ran: bool,
        single_ran: bool,
    }

    #[derive(Resource, Default)]
    struct Counter(u8);

    fn set_single_state(mut _single: Single<&TestComponent>, mut state: ResMut<TestState>) {
        state.single_ran = true;
    }

    fn set_populated_state(
        mut _populated: Populated<&TestComponent>,
        mut state: ResMut<TestState>,
    ) {
        state.populated_ran = true;
    }

    #[test]
    #[expect(clippy::print_stdout, reason = "std and println are allowed in tests")]
    fn single_and_populated_skipped_and_run() {
        for executor in EXECUTORS {
            std::println!("Testing executor: {executor:?}");

            let mut world = World::new();
            world.init_resource::<TestState>();

            let mut schedule = Schedule::default();
            schedule.set_executor_kind(executor);
            schedule.add_systems((set_single_state, set_populated_state));
            schedule.run(&mut world);

            let state = world.get_resource::<TestState>().unwrap();
            assert!(!state.single_ran);
            assert!(!state.populated_ran);

            world.spawn(TestComponent);

            schedule.run(&mut world);
            let state = world.get_resource::<TestState>().unwrap();
            assert!(state.single_ran);
            assert!(state.populated_ran);
        }
    }

    fn look_for_missing_resource(_res: Res<TestState>) {}

    #[test]
    #[should_panic]
    fn missing_resource_panics_single_threaded() {
        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.set_executor_kind(ExecutorKind::SingleThreaded);
        schedule.add_systems(look_for_missing_resource);
        schedule.run(&mut world);
    }

    #[test]
    #[should_panic]
    fn missing_resource_panics_multi_threaded() {
        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.set_executor_kind(ExecutorKind::MultiThreaded);
        schedule.add_systems(look_for_missing_resource);
        schedule.run(&mut world);
    }

    #[test]
    fn piped_systems_first_system_skipped() {
        // This system should be skipped when run due to no matching entity
        fn pipe_out(_single: Single<&TestComponent>) -> u8 {
            42
        }

        fn pipe_in(_input: In<u8>, mut counter: ResMut<Counter>) {
            counter.0 += 1;
        }

        let mut world = World::new();
        world.init_resource::<Counter>();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);

        let counter = world.resource::<Counter>();
        assert_eq!(counter.0, 0);
    }

    #[test]
    fn piped_system_second_system_skipped() {
        // This system will be run before the second system is validated
        fn pipe_out(mut counter: ResMut<Counter>) -> u8 {
            counter.0 += 1;
            42
        }

        // This system should be skipped when run due to no matching entity
        fn pipe_in(_input: In<u8>, _single: Single<&TestComponent>, mut counter: ResMut<Counter>) {
            counter.0 += 1;
        }

        let mut world = World::new();
        world.init_resource::<Counter>();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);
        let counter = world.resource::<Counter>();
        assert_eq!(counter.0, 1);
    }

    #[test]
    #[should_panic]
    fn piped_system_first_system_panics() {
        // This system should panic when run because the resource is missing
        fn pipe_out(_res: Res<TestState>) -> u8 {
            42
        }

        fn pipe_in(_input: In<u8>) {}

        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);
    }

    #[test]
    #[should_panic]
    fn piped_system_second_system_panics() {
        fn pipe_out() -> u8 {
            42
        }

        // This system should panic when run because the resource is missing
        fn pipe_in(_input: In<u8>, _res: Res<TestState>) {}

        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);
    }

    // This test runs without panicking because we've
    // decided to use early-out behavior for piped systems
    #[test]
    fn piped_system_skip_and_panic() {
        // This system should be skipped when run due to no matching entity
        fn pipe_out(_single: Single<&TestComponent>) -> u8 {
            42
        }

        // This system should panic when run because the resource is missing
        fn pipe_in(_input: In<u8>, _res: Res<TestState>) {}

        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);
    }

    #[test]
    #[should_panic]
    fn piped_system_panic_and_skip() {
        // This system should panic when run because the resource is missing

        fn pipe_out(_res: Res<TestState>) -> u8 {
            42
        }

        // This system should be skipped when run due to no matching entity
        fn pipe_in(_input: In<u8>, _single: Single<&TestComponent>) {}

        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);
    }

    #[test]
    #[should_panic]
    fn piped_system_panic_and_panic() {
        // This system should panic when run because the resource is missing

        fn pipe_out(_res: Res<TestState>) -> u8 {
            42
        }

        // This system should panic when run because the resource is missing
        fn pipe_in(_input: In<u8>, _res: Res<TestState>) {}

        let mut world = World::new();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);
    }

    #[test]
    fn piped_system_skip_and_skip() {
        // This system should be skipped when run due to no matching entity

        fn pipe_out(_single: Single<&TestComponent>, mut counter: ResMut<Counter>) -> u8 {
            counter.0 += 1;
            42
        }

        // This system should be skipped when run due to no matching entity
        fn pipe_in(_input: In<u8>, _single: Single<&TestComponent>, mut counter: ResMut<Counter>) {
            counter.0 += 1;
        }

        let mut world = World::new();
        world.init_resource::<Counter>();
        let mut schedule = Schedule::default();

        schedule.add_systems(pipe_out.pipe(pipe_in));
        schedule.run(&mut world);

        let counter = world.resource::<Counter>();
        assert_eq!(counter.0, 0);
    }
}
