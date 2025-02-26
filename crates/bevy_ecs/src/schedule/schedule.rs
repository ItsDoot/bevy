#![expect(
    clippy::module_inception,
    reason = "This instance of module inception is being discussed; see #17344."
)]
use alloc::{boxed::Box, string::ToString};
use core::fmt::{Debug, Write};

use bevy_platform_support::collections::HashMap;
use log::{error, info};
use thiserror::Error;
#[cfg(feature = "trace")]
use tracing::info_span;

use crate::{
    component::{ComponentId, Components, Tick},
    prelude::Component,
    resource::Resource,
    result::{DefaultSystemErrorHandler, Error, SystemErrorContext},
    schedule::{
        default::{DefaultGraph, IgnoredSchedulingAmbiguities, NodeId, ScheduledSystem},
        traits::{EcsScheduleGraph, GraphNode, ScheduleExecutable, ScheduleGraph},
        *,
    },
    world::World,
};

pub use self::stepping::Stepping;

/// Resource that stores [`Schedule`]s mapped to [`ScheduleLabel`]s excluding the current running [`Schedule`].
#[derive(Default, Resource)]
pub struct Schedules<G: ScheduleGraph = DefaultGraph> {
    inner: HashMap<InternedScheduleLabel, Schedule<G>>,
    /// Additional data to be shared between all schedules.
    pub metadata: G::GlobalMetadata,
}

impl<G: ScheduleGraph> Schedules<G> {
    /// Constructs an empty `Schedules` with zero initial capacity.
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts a labeled schedule into the map.
    ///
    /// If the map already had an entry for `label`, `schedule` is inserted,
    /// and the old schedule is returned. Otherwise, `None` is returned.
    pub fn insert(&mut self, schedule: Schedule<G>) -> Option<Schedule<G>> {
        self.inner.insert(schedule.label, schedule)
    }

    /// Removes the schedule corresponding to the `label` from the map, returning it if it existed.
    pub fn remove(&mut self, label: impl ScheduleLabel) -> Option<Schedule<G>> {
        self.inner.remove(&label.intern())
    }

    /// Removes the (schedule, label) pair corresponding to the `label` from the map, returning it if it existed.
    pub fn remove_entry(
        &mut self,
        label: impl ScheduleLabel,
    ) -> Option<(InternedScheduleLabel, Schedule<G>)> {
        self.inner.remove_entry(&label.intern())
    }

    /// Does a schedule with the provided label already exist?
    pub fn contains(&self, label: impl ScheduleLabel) -> bool {
        self.inner.contains_key(&label.intern())
    }

    /// Returns a reference to the schedule associated with `label`, if it exists.
    pub fn get(&self, label: impl ScheduleLabel) -> Option<&Schedule<G>> {
        self.inner.get(&label.intern())
    }

    /// Returns a mutable reference to the schedule associated with `label`, if it exists.
    pub fn get_mut(&mut self, label: impl ScheduleLabel) -> Option<&mut Schedule<G>> {
        self.inner.get_mut(&label.intern())
    }

    /// Returns a mutable reference to the schedules associated with `label`, creating one if it doesn't already exist.
    pub fn entry(&mut self, label: impl ScheduleLabel) -> &mut Schedule<G> {
        self.inner
            .entry(label.intern())
            .or_insert_with(|| Schedule::new(label))
    }

    /// Returns an iterator over all schedules. Iteration order is undefined.
    pub fn iter(&self) -> impl Iterator<Item = (&dyn ScheduleLabel, &Schedule<G>)> {
        self.inner
            .iter()
            .map(|(label, schedule)| (&**label, schedule))
    }
    /// Returns an iterator over mutable references to all schedules. Iteration order is undefined.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&dyn ScheduleLabel, &mut Schedule<G>)> {
        self.inner
            .iter_mut()
            .map(|(label, schedule)| (&**label, schedule))
    }

    /// Iterates the change ticks of all systems in all stored schedules and clamps any older than
    /// [`MAX_CHANGE_AGE`](crate::change_detection::MAX_CHANGE_AGE).
    /// This prevents overflow and thus prevents false positives.
    pub(crate) fn check_change_ticks(&mut self, change_tick: Tick) {
        #[cfg(feature = "trace")]
        let _all_span = info_span!("check stored schedule ticks").entered();
        #[cfg_attr(
            not(feature = "trace"),
            expect(
                unused_variables,
                reason = "The `label` variable goes unused if the `trace` feature isn't active"
            )
        )]
        for (label, schedule) in &mut self.inner {
            #[cfg(feature = "trace")]
            let name = format!("{label:?}");
            #[cfg(feature = "trace")]
            let _one_span = info_span!("check schedule ticks", name = &name).entered();
            schedule.check_change_ticks(change_tick);
        }
    }

    /// Applies the provided [`ScheduleBuildSettings`] to all schedules.
    pub fn configure_schedules(&mut self, build_settings: G::BuildSettings) {
        for (_, schedule) in &mut self.inner {
            schedule.set_build_settings(build_settings.clone());
        }
    }

    /// Processes configured nodes and adds them to the schedule with the provided label.
    pub fn process_nodes<N: GraphNode<G>, M>(
        &mut self,
        schedule: impl ScheduleLabel,
        nodes: impl IntoNodeConfigs<N, G, M>,
    ) -> &mut Self {
        self.entry(schedule).process_nodes(nodes);
        self
    }

    /// Adds one or more systems to the [`Schedule`] matching the provided [`ScheduleLabel`].
    pub fn add_systems<M>(
        &mut self,
        schedule: impl ScheduleLabel,
        systems: impl IntoNodeConfigs<FallibleSystem, G, M>,
    ) -> &mut Self
    where
        FallibleSystem: GraphNode<G>,
    {
        self.process_nodes(schedule, systems)
    }

    /// Configures a collection of system sets in the provided schedule, adding any sets that do not exist.
    #[track_caller]
    pub fn configure_sets<M>(
        &mut self,
        schedule: impl ScheduleLabel,
        sets: impl IntoNodeConfigs<InternedSystemSet, G, M>,
    ) -> &mut Self
    where
        InternedSystemSet: GraphNode<G>,
    {
        self.process_nodes(schedule, sets)
    }
}

impl<G: ScheduleGraph<GlobalMetadata = IgnoredSchedulingAmbiguities>> Schedules<G> {
    /// Ignore system order ambiguities caused by conflicts on [`Component`]s of type `T`.
    pub fn allow_ambiguous_component<T: Component>(&mut self, world: &mut World) {
        self.metadata.insert(world.register_component::<T>());
    }

    /// Ignore system order ambiguities caused by conflicts on [`Resource`]s of type `T`.
    pub fn allow_ambiguous_resource<T: Resource>(&mut self, world: &mut World) {
        self.metadata
            .insert(world.components.register_resource::<T>());
    }

    /// Iterate through the [`ComponentId`]'s that will be ignored.
    pub fn iter_ignored_ambiguities(&self) -> impl Iterator<Item = &ComponentId> + '_ {
        self.metadata.iter()
    }

    /// Prints the names of the components and resources with [`info`]
    ///
    /// May panic or retrieve incorrect names if [`Components`] is not from the same
    /// world
    pub fn print_ignored_ambiguities(&self, components: &Components) {
        let mut message =
            "System order ambiguities caused by conflicts on the following types are ignored:\n"
                .to_string();
        for id in self.iter_ignored_ambiguities() {
            writeln!(message, "{}", components.get_name(*id).unwrap()).unwrap();
        }

        info!("{}", message);
    }
}

impl Schedules {
    /// Suppress warnings and errors that would result from systems in these sets having ambiguities
    /// (conflicting access but indeterminate order) with systems in `set`.
    ///
    /// When possible, do this directly in the `.add_systems(Update, a.ambiguous_with(b))` call.
    /// However, sometimes two independent plugins `A` and `B` are reported as ambiguous, which you
    /// can only suppress as the consumer of both.
    #[track_caller]
    pub fn ignore_ambiguity<M1, M2, S1, S2>(
        &mut self,
        schedule: impl ScheduleLabel,
        a: S1,
        b: S2,
    ) -> &mut Self
    where
        S1: IntoSystemSet<M1>,
        S2: IntoSystemSet<M2>,
    {
        self.entry(schedule).ignore_ambiguity(a, b);

        self
    }
}

/// A collection of systems, and the metadata and executor needed to run them
/// in a certain order under certain conditions.
///
/// # Example
/// Here is an example of a `Schedule` running a "Hello world" system:
/// ```
/// # use bevy_ecs::prelude::*;
/// fn hello_world() { println!("Hello world!") }
///
/// fn main() {
///     let mut world = World::new();
///     let mut schedule = Schedule::default();
///     schedule.add_systems(hello_world);
///
///     schedule.run(&mut world);
/// }
/// ```
///
/// A schedule can also run several systems in an ordered way:
/// ```
/// # use bevy_ecs::prelude::*;
/// fn system_one() { println!("System 1 works!") }
/// fn system_two() { println!("System 2 works!") }
/// fn system_three() { println!("System 3 works!") }
///
/// fn main() {
///     let mut world = World::new();
///     let mut schedule = Schedule::default();
///     schedule.add_systems((
///         system_two,
///         system_one.before(system_two),
///         system_three.after(system_two),
///     ));
///
///     schedule.run(&mut world);
/// }
/// ```
pub struct Schedule<G: ScheduleGraph = DefaultGraph> {
    label: InternedScheduleLabel,
    graph: G,
    executable: G::Executable,
    executor: Box<dyn ScheduleExecutor<G>>,
    executor_initialized: bool,
    error_handler: Option<fn(Error, SystemErrorContext)>,
}

#[derive(ScheduleLabel, Hash, PartialEq, Eq, Debug, Clone)]
struct DefaultSchedule;

impl Default for Schedule {
    /// Creates a schedule with a default label. Only use in situations where
    /// you don't care about the [`ScheduleLabel`]. Inserting a default schedule
    /// into the world risks overwriting another schedule. For most situations
    /// you should use [`Schedule::new`].
    fn default() -> Self {
        Self::new(DefaultSchedule)
    }
}

impl<G: ScheduleGraph> Schedule<G> {
    /// Constructs an empty `Schedule`.
    pub fn new(label: impl ScheduleLabel) -> Self {
        let mut this = Self {
            label: label.intern(),
            graph: G::default(),
            executable: G::Executable::default(),
            executor: G::new_executor(G::ExecutorKind::default()),
            executor_initialized: false,
            error_handler: None,
        };
        // Call `set_build_settings` to add any default build passes
        this.set_build_settings(Default::default());
        this
    }

    /// Get the `InternedScheduleLabel` for this `Schedule`.
    pub fn label(&self) -> InternedScheduleLabel {
        self.label
    }

    /// Processes configured nodes and adds them to the graph.
    pub fn process_nodes<N: GraphNode<G>, M>(
        &mut self,
        nodes: impl IntoNodeConfigs<N, G, M>,
    ) -> &mut Self {
        N::process_configs(&mut self.graph, nodes.into_configs(), false).unwrap();
        self
    }

    /// Add a collection of systems to the schedule.
    pub fn add_systems<M>(
        &mut self,
        systems: impl IntoNodeConfigs<FallibleSystem, G, M>,
    ) -> &mut Self
    where
        FallibleSystem: GraphNode<G>,
    {
        self.process_nodes(systems)
    }

    /// Configures a collection of system sets in this schedule, adding them if they does not exist.
    #[track_caller]
    pub fn configure_sets<M>(
        &mut self,
        sets: impl IntoNodeConfigs<InternedSystemSet, G, M>,
    ) -> &mut Self
    where
        InternedSystemSet: GraphNode<G>,
    {
        self.process_nodes(sets)
    }

    /// Add a custom build pass to the schedule.
    pub fn add_build_pass<T: ScheduleBuildPass<G>>(&mut self, pass: T) -> &mut Self {
        self.graph.add_build_pass(pass);
        self
    }

    /// Remove a custom build pass.
    pub fn remove_build_pass<T: ScheduleBuildPass<G>>(&mut self) {
        self.graph.remove_build_pass::<T>();
    }

    /// Changes miscellaneous build settings.
    pub fn set_build_settings(&mut self, settings: G::BuildSettings) -> &mut Self {
        self.graph.set_build_settings(settings);
        self
    }

    /// Set the error handler to use for systems that return a [`Result`](crate::result::Result).
    ///
    /// See the [`result` module-level documentation](crate::result) for more information.
    pub fn set_error_handler(&mut self, error_handler: fn(Error, SystemErrorContext)) {
        self.error_handler = Some(error_handler);
    }

    /// Returns the schedule's current build settings.
    pub fn get_build_settings(&self) -> G::BuildSettings {
        self.graph.get_build_settings().clone()
    }

    /// Returns the schedule's current execution strategy.
    pub fn get_executor_kind(&self) -> G::ExecutorKind {
        self.executor.kind()
    }

    /// Sets the schedule's execution strategy.
    pub fn set_executor_kind(&mut self, executor: G::ExecutorKind) -> &mut Self {
        if executor != self.executor.kind() {
            self.executor = G::new_executor(executor);
            self.executor_initialized = false;
        }
        self
    }

    /// Set whether the schedule applies deferred system buffers on final time or not. This is a catch-all
    /// in case a system uses commands but was not explicitly ordered before an instance of
    /// [`ApplyDeferred`]. By default this
    /// setting is true, but may be disabled if needed.
    pub fn set_apply_final_deferred(&mut self, apply_final_deferred: bool) -> &mut Self {
        self.executor.set_apply_final_deferred(apply_final_deferred);
        self
    }

    /// Runs all systems in this schedule on the `world`, using its current execution strategy.
    pub fn run_with(
        &mut self,
        world: &mut World,
        global_metadata: impl FnOnce(&mut World) -> G::GlobalMetadata,
    ) {
        #[cfg(feature = "trace")]
        let _span = info_span!("schedule", name = ?self.label).entered();

        world.check_change_ticks();
        self.initialize_with(world, global_metadata)
            .unwrap_or_else(|e| panic!("Error when initializing schedule {:?}: {e}", self.label));

        let error_handler = self.error_handler.expect("schedule initialized");

        #[cfg(not(feature = "bevy_debug_stepping"))]
        self.executor
            .run(&mut self.executable, world, None, error_handler);

        #[cfg(feature = "bevy_debug_stepping")]
        {
            let skip_systems = match world.get_resource_mut::<Stepping>() {
                None => None,
                Some(mut stepping) => stepping.skipped_systems(self),
            };

            self.executor.run(
                &mut self.executable,
                world,
                skip_systems.as_ref(),
                error_handler,
            );
        }
    }

    /// Initializes any newly-added systems and conditions, rebuilds the executable schedule,
    /// and re-initializes the executor.
    ///
    /// Moves all systems and run conditions out of the [`ScheduleGraph`].
    pub fn initialize_with(
        &mut self,
        world: &mut World,
        global_metadata: impl FnOnce(&mut World) -> G::GlobalMetadata,
    ) -> Result<(), G::BuildError> {
        if self.graph.changed() {
            self.graph.initialize(world);
            let global_metadata = global_metadata(world);
            self.graph
                .update(world, &mut self.executable, &global_metadata, self.label)?;
            self.graph.set_changed(false);
            self.executor_initialized = false;
        }

        if self.error_handler.is_none() {
            self.error_handler = Some(world.get_resource_or_init::<DefaultSystemErrorHandler>().0);
        }

        if !self.executor_initialized {
            self.executor.init(&self.executable);
            self.executor_initialized = true;
        }

        Ok(())
    }

    /// Returns the [`ScheduleGraph`].
    pub fn graph(&self) -> &G {
        &self.graph
    }

    /// Returns a mutable reference to the [`ScheduleGraph`].
    pub fn graph_mut(&mut self) -> &mut G {
        &mut self.graph
    }

    /// Returns the [`SystemSchedule`].
    pub(crate) fn executable(&self) -> &G::Executable {
        &self.executable
    }

    /// Iterates the change ticks of all systems in the schedule and clamps any older than
    /// [`MAX_CHANGE_AGE`](crate::change_detection::MAX_CHANGE_AGE).
    /// This prevents overflow and thus prevents false positives.
    pub(crate) fn check_change_ticks(&mut self, change_tick: Tick) {
        self.executable.check_change_ticks(change_tick);
    }

    /// Directly applies any accumulated [`Deferred`](crate::system::Deferred) system parameters (like [`Commands`](crate::prelude::Commands)) to the `world`.
    ///
    /// Like always, deferred system parameters are applied in the "topological sort order" of the schedule graph.
    /// As a result, buffers from one system are only guaranteed to be applied before those of other systems
    /// if there is an explicit system ordering between the two systems.
    ///
    /// This is used in rendering to extract data from the main world, storing the data in system buffers,
    /// before applying their buffers in a different world.
    pub fn apply_deferred(&mut self, world: &mut World) {
        self.executable.apply_deferred(world);
    }
}

impl<G: EcsScheduleGraph> Schedule<G> {
    /// Runs all systems in this schedule on the `world`, using its current execution strategy.
    pub fn run(&mut self, world: &mut World) {
        self.run_with(world, |world| {
            world
                .get_resource_or_init::<Schedules<G>>()
                .metadata
                .clone()
        });
    }

    /// Initializes any newly-added systems and conditions, rebuilds the executable schedule,
    /// and re-initializes the executor.
    ///
    /// Moves all systems and run conditions out of the [`ScheduleGraph`].
    pub fn initialize(&mut self, world: &mut World) -> Result<(), G::BuildError> {
        self.initialize_with(world, |world| {
            world
                .get_resource_or_init::<Schedules<G>>()
                .metadata
                .clone()
        })
    }
}

impl Schedule {
    /// Suppress warnings and errors that would result from systems in these sets having ambiguities
    /// (conflicting access but indeterminate order) with systems in `set`.
    #[track_caller]
    pub fn ignore_ambiguity<M1, M2, S1, S2>(&mut self, a: S1, b: S2) -> &mut Self
    where
        S1: IntoSystemSet<M1>,
        S2: IntoSystemSet<M2>,
    {
        let a = a.into_system_set();
        let b = b.into_system_set();

        let Some(&a_id) = self.graph.system_set_ids.get(&a.intern()) else {
            panic!(
                "Could not mark system as ambiguous, `{:?}` was not found in the schedule.
                Did you try to call `ambiguous_with` before adding the system to the world?",
                a
            );
        };
        let Some(&b_id) = self.graph.system_set_ids.get(&b.intern()) else {
            panic!(
                "Could not mark system as ambiguous, `{:?}` was not found in the schedule.
                Did you try to call `ambiguous_with` before adding the system to the world?",
                b
            );
        };

        self.graph.ambiguous_with.add_edge(a_id, b_id);

        self
    }

    /// Returns an iterator over all systems in this schedule.
    ///
    /// Note: this method will return [`ScheduleNotInitialized`] if the
    /// schedule has never been initialized or run.
    pub fn systems(
        &self,
    ) -> Result<impl Iterator<Item = (NodeId, &ScheduledSystem)> + Sized, ScheduleNotInitialized>
    {
        if !self.executor_initialized {
            return Err(ScheduleNotInitialized);
        }

        let iter = self
            .executable
            .system_ids
            .iter()
            .zip(&self.executable.systems)
            .map(|(node_id, system)| (*node_id, system));

        Ok(iter)
    }

    /// Returns the number of systems in this schedule.
    pub fn systems_len(&self) -> usize {
        if !self.executor_initialized {
            self.graph.systems.len()
        } else {
            self.executable.systems.len()
        }
    }
}

/// Used to select the appropriate reporting function.
pub enum ReportCycles {
    /// When sets contain themselves
    Hierarchy,
    /// When the graph is no longer a DAG
    Dependency,
}

/// Error to denote that [`Schedule::initialize`] or [`Schedule::run`] has not yet been called for
/// this schedule.
#[derive(Error, Debug)]
#[error("executable schedule has not been built")]
pub struct ScheduleNotInitialized;

#[cfg(test)]
mod tests {
    use bevy_ecs_macros::ScheduleLabel;

    use crate::{
        prelude::{ApplyDeferred, Res, Resource},
        schedule::{
            default::{
                DefaultBuildSettings, IntoChainableNodeConfigs, IntoConditionalNodeConfigs,
                IntoOrderedNodeConfigs,
            },
            tests::ResMut,
            Schedule, SystemSet,
        },
        system::Commands,
        world::World,
    };

    use super::Schedules;

    #[derive(Resource)]
    struct Resource1;

    #[derive(Resource)]
    struct Resource2;

    // regression test for https://github.com/bevyengine/bevy/issues/9114
    #[test]
    fn ambiguous_with_not_breaking_run_conditions() {
        #[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
        struct Set;

        let mut world = World::new();
        let mut schedule = Schedule::default();

        let system: fn() = || {
            panic!("This system must not run");
        };

        schedule.configure_sets(Set.run_if(|| false));
        schedule.add_systems(system.ambiguous_with(|| ()).in_set(Set));
        schedule.run(&mut world);
    }

    #[test]
    fn inserts_a_sync_point() {
        let mut schedule = Schedule::default();
        let mut world = World::default();
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |_: Res<Resource1>| {},
            )
                .chain(),
        );
        schedule.run(&mut world);

        // inserted a sync point
        assert_eq!(schedule.executable.systems.len(), 3);
    }

    #[test]
    fn explicit_sync_point_used_as_auto_sync_point() {
        let mut schedule = Schedule::default();
        let mut world = World::default();
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |_: Res<Resource1>| {},
            )
                .chain(),
        );
        schedule.add_systems((|| {}, ApplyDeferred, || {}).chain());
        schedule.run(&mut world);

        // No sync point was inserted, since we can reuse the explicit sync point.
        assert_eq!(schedule.executable.systems.len(), 5);
    }

    #[test]
    fn conditional_explicit_sync_point_not_used_as_auto_sync_point() {
        let mut schedule = Schedule::default();
        let mut world = World::default();
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |_: Res<Resource1>| {},
            )
                .chain(),
        );
        schedule.add_systems((|| {}, ApplyDeferred.run_if(|| false), || {}).chain());
        schedule.run(&mut world);

        // A sync point was inserted, since the explicit sync point is not always run.
        assert_eq!(schedule.executable.systems.len(), 6);
    }

    #[test]
    fn conditional_explicit_sync_point_not_used_as_auto_sync_point_condition_on_chain() {
        let mut schedule = Schedule::default();
        let mut world = World::default();
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |_: Res<Resource1>| {},
            )
                .chain(),
        );
        schedule.add_systems((|| {}, ApplyDeferred, || {}).chain().run_if(|| false));
        schedule.run(&mut world);

        // A sync point was inserted, since the explicit sync point is not always run.
        assert_eq!(schedule.executable.systems.len(), 6);
    }

    #[test]
    fn conditional_explicit_sync_point_not_used_as_auto_sync_point_condition_on_system_set() {
        #[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
        struct Set;

        let mut schedule = Schedule::default();
        let mut world = World::default();
        schedule.configure_sets(Set.run_if(|| false));
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |_: Res<Resource1>| {},
            )
                .chain(),
        );
        schedule.add_systems((|| {}, ApplyDeferred.in_set(Set), || {}).chain());
        schedule.run(&mut world);

        // A sync point was inserted, since the explicit sync point is not always run.
        assert_eq!(schedule.executable.systems.len(), 6);
    }

    #[test]
    fn conditional_explicit_sync_point_not_used_as_auto_sync_point_condition_on_nested_system_set()
    {
        #[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
        struct Set1;
        #[derive(SystemSet, Debug, Clone, PartialEq, Eq, Hash)]
        struct Set2;

        let mut schedule = Schedule::default();
        let mut world = World::default();
        schedule.configure_sets(Set2.run_if(|| false));
        schedule.configure_sets(Set1.in_set(Set2));
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |_: Res<Resource1>| {},
            )
                .chain(),
        );
        schedule.add_systems((|| {}, ApplyDeferred, || {}).chain().in_set(Set1));
        schedule.run(&mut world);

        // A sync point was inserted, since the explicit sync point is not always run.
        assert_eq!(schedule.executable.systems.len(), 6);
    }

    #[test]
    fn merges_sync_points_into_one() {
        let mut schedule = Schedule::default();
        let mut world = World::default();
        // insert two parallel command systems, it should only create one sync point
        schedule.add_systems(
            (
                (
                    |mut commands: Commands| commands.insert_resource(Resource1),
                    |mut commands: Commands| commands.insert_resource(Resource2),
                ),
                |_: Res<Resource1>, _: Res<Resource2>| {},
            )
                .chain(),
        );
        schedule.run(&mut world);

        // inserted sync points
        assert_eq!(schedule.executable.systems.len(), 4);

        // merges sync points on rebuild
        schedule.add_systems(((
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |mut commands: Commands| commands.insert_resource(Resource2),
            ),
            |_: Res<Resource1>, _: Res<Resource2>| {},
        )
            .chain(),));
        schedule.run(&mut world);

        assert_eq!(schedule.executable.systems.len(), 7);
    }

    #[test]
    fn adds_multiple_consecutive_syncs() {
        let mut schedule = Schedule::default();
        let mut world = World::default();
        // insert two consecutive command systems, it should create two sync points
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |mut commands: Commands| commands.insert_resource(Resource2),
                |_: Res<Resource1>, _: Res<Resource2>| {},
            )
                .chain(),
        );
        schedule.run(&mut world);

        assert_eq!(schedule.executable.systems.len(), 5);
    }

    #[test]
    fn disable_auto_sync_points() {
        let mut schedule = Schedule::default();
        schedule.set_build_settings(DefaultBuildSettings {
            auto_insert_apply_deferred: false,
            ..Default::default()
        });
        let mut world = World::default();
        schedule.add_systems(
            (
                |mut commands: Commands| commands.insert_resource(Resource1),
                |res: Option<Res<Resource1>>| assert!(res.is_none()),
            )
                .chain(),
        );
        schedule.run(&mut world);

        assert_eq!(schedule.executable.systems.len(), 2);
    }

    mod no_sync_edges {
        use super::*;

        fn insert_resource(mut commands: Commands) {
            commands.insert_resource(Resource1);
        }

        fn resource_does_not_exist(res: Option<Res<Resource1>>) {
            assert!(res.is_none());
        }

        #[derive(SystemSet, Hash, PartialEq, Eq, Debug, Clone)]
        enum Sets {
            A,
            B,
        }

        fn check_no_sync_edges(add_systems: impl FnOnce(&mut Schedule)) {
            let mut schedule = Schedule::default();
            let mut world = World::default();
            add_systems(&mut schedule);

            schedule.run(&mut world);

            assert_eq!(schedule.executable.systems.len(), 2);
        }

        #[test]
        fn system_to_system_after() {
            check_no_sync_edges(|schedule| {
                schedule.add_systems((
                    insert_resource,
                    resource_does_not_exist.after_ignore_deferred(insert_resource),
                ));
            });
        }

        #[test]
        fn system_to_system_before() {
            check_no_sync_edges(|schedule| {
                schedule.add_systems((
                    insert_resource.before_ignore_deferred(resource_does_not_exist),
                    resource_does_not_exist,
                ));
            });
        }

        #[test]
        fn set_to_system_after() {
            check_no_sync_edges(|schedule| {
                schedule
                    .add_systems((insert_resource, resource_does_not_exist.in_set(Sets::A)))
                    .configure_sets(Sets::A.after_ignore_deferred(insert_resource));
            });
        }

        #[test]
        fn set_to_system_before() {
            check_no_sync_edges(|schedule| {
                schedule
                    .add_systems((insert_resource.in_set(Sets::A), resource_does_not_exist))
                    .configure_sets(Sets::A.before_ignore_deferred(resource_does_not_exist));
            });
        }

        #[test]
        fn set_to_set_after() {
            check_no_sync_edges(|schedule| {
                schedule
                    .add_systems((
                        insert_resource.in_set(Sets::A),
                        resource_does_not_exist.in_set(Sets::B),
                    ))
                    .configure_sets(Sets::B.after_ignore_deferred(Sets::A));
            });
        }

        #[test]
        fn set_to_set_before() {
            check_no_sync_edges(|schedule| {
                schedule
                    .add_systems((
                        insert_resource.in_set(Sets::A),
                        resource_does_not_exist.in_set(Sets::B),
                    ))
                    .configure_sets(Sets::A.before_ignore_deferred(Sets::B));
            });
        }
    }

    mod no_sync_chain {
        use super::*;

        #[derive(Resource)]
        struct Ra;

        #[derive(Resource)]
        struct Rb;

        #[derive(Resource)]
        struct Rc;

        fn run_schedule(expected_num_systems: usize, add_systems: impl FnOnce(&mut Schedule)) {
            let mut schedule = Schedule::default();
            let mut world = World::default();
            add_systems(&mut schedule);

            schedule.run(&mut world);

            assert_eq!(schedule.executable.systems.len(), expected_num_systems);
        }

        #[test]
        fn only_chain_outside() {
            run_schedule(5, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands| commands.insert_resource(Rb),
                        ),
                        (
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                            },
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                            },
                        ),
                    )
                        .chain(),
                );
            });

            run_schedule(4, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands| commands.insert_resource(Rb),
                        ),
                        (
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_none());
                                assert!(res_b.is_none());
                            },
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_none());
                                assert!(res_b.is_none());
                            },
                        ),
                    )
                        .chain_ignore_deferred(),
                );
            });
        }

        #[test]
        fn chain_first() {
            run_schedule(6, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands, res_a: Option<Res<Ra>>| {
                                commands.insert_resource(Rb);
                                assert!(res_a.is_some());
                            },
                        )
                            .chain(),
                        (
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                            },
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                            },
                        ),
                    )
                        .chain(),
                );
            });

            run_schedule(5, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands, res_a: Option<Res<Ra>>| {
                                commands.insert_resource(Rb);
                                assert!(res_a.is_some());
                            },
                        )
                            .chain(),
                        (
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_none());
                            },
                            |res_a: Option<Res<Ra>>, res_b: Option<Res<Rb>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_none());
                            },
                        ),
                    )
                        .chain_ignore_deferred(),
                );
            });
        }

        #[test]
        fn chain_second() {
            run_schedule(6, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands| commands.insert_resource(Rb),
                        ),
                        (
                            |mut commands: Commands,
                             res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>| {
                                commands.insert_resource(Rc);
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                            },
                            |res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>,
                             res_c: Option<Res<Rc>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                                assert!(res_c.is_some());
                            },
                        )
                            .chain(),
                    )
                        .chain(),
                );
            });

            run_schedule(5, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands| commands.insert_resource(Rb),
                        ),
                        (
                            |mut commands: Commands,
                             res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>| {
                                commands.insert_resource(Rc);
                                assert!(res_a.is_none());
                                assert!(res_b.is_none());
                            },
                            |res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>,
                             res_c: Option<Res<Rc>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                                assert!(res_c.is_some());
                            },
                        )
                            .chain(),
                    )
                        .chain_ignore_deferred(),
                );
            });
        }

        #[test]
        fn chain_all() {
            run_schedule(7, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands, res_a: Option<Res<Ra>>| {
                                commands.insert_resource(Rb);
                                assert!(res_a.is_some());
                            },
                        )
                            .chain(),
                        (
                            |mut commands: Commands,
                             res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>| {
                                commands.insert_resource(Rc);
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                            },
                            |res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>,
                             res_c: Option<Res<Rc>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                                assert!(res_c.is_some());
                            },
                        )
                            .chain(),
                    )
                        .chain(),
                );
            });

            run_schedule(6, |schedule: &mut Schedule| {
                schedule.add_systems(
                    (
                        (
                            |mut commands: Commands| commands.insert_resource(Ra),
                            |mut commands: Commands, res_a: Option<Res<Ra>>| {
                                commands.insert_resource(Rb);
                                assert!(res_a.is_some());
                            },
                        )
                            .chain(),
                        (
                            |mut commands: Commands,
                             res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>| {
                                commands.insert_resource(Rc);
                                assert!(res_a.is_some());
                                assert!(res_b.is_none());
                            },
                            |res_a: Option<Res<Ra>>,
                             res_b: Option<Res<Rb>>,
                             res_c: Option<Res<Rc>>| {
                                assert!(res_a.is_some());
                                assert!(res_b.is_some());
                                assert!(res_c.is_some());
                            },
                        )
                            .chain(),
                    )
                        .chain_ignore_deferred(),
                );
            });
        }
    }

    #[derive(ScheduleLabel, Hash, Debug, Clone, PartialEq, Eq)]
    struct TestSchedule;

    #[derive(Resource)]
    struct CheckSystemRan(usize);

    #[test]
    fn add_systems_to_existing_schedule() {
        let mut schedules = Schedules::default();
        let schedule = Schedule::new(TestSchedule);

        schedules.insert(schedule);
        schedules.add_systems(TestSchedule, |mut ran: ResMut<CheckSystemRan>| ran.0 += 1);

        let mut world = World::new();

        world.insert_resource(CheckSystemRan(0));
        world.insert_resource(schedules);
        world.run_schedule(TestSchedule);

        let value = world
            .get_resource::<CheckSystemRan>()
            .expect("CheckSystemRan Resource Should Exist");
        assert_eq!(value.0, 1);
    }

    #[test]
    fn add_systems_to_non_existing_schedule() {
        let mut schedules = Schedules::default();

        schedules.add_systems(TestSchedule, |mut ran: ResMut<CheckSystemRan>| ran.0 += 1);

        let mut world = World::new();

        world.insert_resource(CheckSystemRan(0));
        world.insert_resource(schedules);
        world.run_schedule(TestSchedule);

        let value = world
            .get_resource::<CheckSystemRan>()
            .expect("CheckSystemRan Resource Should Exist");
        assert_eq!(value.0, 1);
    }

    #[derive(SystemSet, Debug, Hash, Clone, PartialEq, Eq)]
    enum TestSet {
        First,
        Second,
    }

    #[test]
    fn configure_set_on_existing_schedule() {
        let mut schedules = Schedules::default();
        let schedule = Schedule::new(TestSchedule);

        schedules.insert(schedule);

        schedules.configure_sets(TestSchedule, (TestSet::First, TestSet::Second).chain());
        schedules.add_systems(
            TestSchedule,
            (|mut ran: ResMut<CheckSystemRan>| {
                assert_eq!(ran.0, 0);
                ran.0 += 1;
            })
            .in_set(TestSet::First),
        );

        schedules.add_systems(
            TestSchedule,
            (|mut ran: ResMut<CheckSystemRan>| {
                assert_eq!(ran.0, 1);
                ran.0 += 1;
            })
            .in_set(TestSet::Second),
        );

        let mut world = World::new();

        world.insert_resource(CheckSystemRan(0));
        world.insert_resource(schedules);
        world.run_schedule(TestSchedule);

        let value = world
            .get_resource::<CheckSystemRan>()
            .expect("CheckSystemRan Resource Should Exist");
        assert_eq!(value.0, 2);
    }

    #[test]
    fn configure_set_on_new_schedule() {
        let mut schedules = Schedules::default();

        schedules.configure_sets(TestSchedule, (TestSet::First, TestSet::Second).chain());
        schedules.add_systems(
            TestSchedule,
            (|mut ran: ResMut<CheckSystemRan>| {
                assert_eq!(ran.0, 0);
                ran.0 += 1;
            })
            .in_set(TestSet::First),
        );

        schedules.add_systems(
            TestSchedule,
            (|mut ran: ResMut<CheckSystemRan>| {
                assert_eq!(ran.0, 1);
                ran.0 += 1;
            })
            .in_set(TestSet::Second),
        );

        let mut world = World::new();

        world.insert_resource(CheckSystemRan(0));
        world.insert_resource(schedules);
        world.run_schedule(TestSchedule);

        let value = world
            .get_resource::<CheckSystemRan>()
            .expect("CheckSystemRan Resource Should Exist");
        assert_eq!(value.0, 2);
    }
}
