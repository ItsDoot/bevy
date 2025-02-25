#[cfg(feature = "std")]
mod multi_threaded;
mod simple;
mod single_threaded;

use alloc::{borrow::Cow, vec, vec::Vec};
use core::any::TypeId;

pub use self::{simple::SimpleExecutor, single_threaded::SingleThreadedExecutor};

#[cfg(feature = "std")]
pub use self::multi_threaded::{MainThreadExecutor, MultiThreadedExecutor};

use fixedbitset::FixedBitSet;

use crate::{
    archetype::ArchetypeComponentId,
    component::{ComponentId, Tick},
    prelude::{IntoSystemSet, SystemSet},
    query::Access,
    result::{Error, Result, SystemErrorContext},
    schedule::{default::ScheduledSystem, traits::ScheduleGraph, InternedSystemSet, SystemTypeSet},
    system::{System, SystemIn},
    world::{unsafe_world_cell::UnsafeWorldCell, DeferredWorld, World},
};

/// Types that can run a [`DefaultGraphExecutable`] on a [`World`].
///
/// [`DefaultGraphExecutable`]: crate::schedule::default::DefaultGraphExecutable
pub trait ScheduleExecutor<G: ScheduleGraph>: Send + Sync {
    /// The kind of executor.
    fn kind(&self) -> G::ExecutorKind;

    /// Initializes the executor with the given [`Executable`].
    fn init(&mut self, schedule: &G::Executable);

    /// Runs the [`Executable`] on the given [`World`].
    fn run(
        &mut self,
        schedule: &mut G::Executable,
        world: &mut World,
        skip_systems: Option<&FixedBitSet>,
        error_handler: fn(Error, SystemErrorContext),
    );

    /// Sets whether the executor should apply deferred system buffers at the
    /// end of the schedule run.
    fn set_apply_final_deferred(&mut self, value: bool);
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
    #[cfg_attr(any(target_arch = "wasm32", not(feature = "multi_threaded")), default)]
    SingleThreaded,
    /// Like [`SingleThreaded`](ExecutorKind::SingleThreaded) but calls [`apply_deferred`](crate::system::System::apply_deferred)
    /// immediately after running each system.
    Simple,
    /// Runs the schedule using a thread pool. Non-conflicting systems can run in parallel.
    #[cfg(feature = "std")]
    #[cfg_attr(all(not(target_arch = "wasm32"), feature = "multi_threaded"), default)]
    MultiThreaded,
}

/// See [`ApplyDeferred`].
#[deprecated(
    since = "0.16.0",
    note = "Use `ApplyDeferred` instead. This was previously a function but is now a marker struct System."
)]
#[expect(
    non_upper_case_globals,
    reason = "This item is deprecated; as such, its previous name needs to stay."
)]
pub const apply_deferred: ApplyDeferred = ApplyDeferred;

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

/// Returns `true` if the [`System`] is an instance of [`ApplyDeferred`].
pub(super) fn is_apply_deferred(system: &ScheduledSystem) -> bool {
    system.type_id() == TypeId::of::<ApplyDeferred>()
}

impl System for ApplyDeferred {
    type In = ();
    type Out = Result<()>;

    fn name(&self) -> Cow<'static, str> {
        Cow::Borrowed("bevy_ecs::apply_deferred")
    }

    fn component_access(&self) -> &Access<ComponentId> {
        // This system accesses no components.
        const { &Access::new() }
    }

    fn archetype_component_access(&self) -> &Access<ArchetypeComponentId> {
        // This system accesses no archetype components.
        const { &Access::new() }
    }

    fn is_send(&self) -> bool {
        // Although this system itself does nothing on its own, the system
        // executor uses it to apply deferred commands. Commands must be allowed
        // to access non-send resources, so this system must be non-send for
        // scheduling purposes.
        false
    }

    fn is_exclusive(&self) -> bool {
        // This system is labeled exclusive because it is used by the system
        // executor to find places where deferred commands should be applied,
        // and commands can only be applied with exclusive access to the world.
        true
    }

    fn has_deferred(&self) -> bool {
        // This system itself doesn't have any commands to apply, but when it
        // is pulled from the schedule to be ran, the executor will apply
        // deferred commands from other systems.
        false
    }

    unsafe fn run_unsafe(
        &mut self,
        _input: SystemIn<'_, Self>,
        _world: UnsafeWorldCell,
    ) -> Self::Out {
        // This system does nothing on its own. The executor will apply deferred
        // commands from other systems instead of running this system.
        Ok(())
    }

    fn run(&mut self, _input: SystemIn<'_, Self>, _world: &mut World) -> Self::Out {
        // This system does nothing on its own. The executor will apply deferred
        // commands from other systems instead of running this system.
        Ok(())
    }

    fn apply_deferred(&mut self, _world: &mut World) {}

    fn queue_deferred(&mut self, _world: DeferredWorld) {}

    unsafe fn validate_param_unsafe(&mut self, _world: UnsafeWorldCell) -> bool {
        // This system is always valid to run because it doesn't do anything,
        // and only used as a marker for the executor.
        true
    }

    fn initialize(&mut self, _world: &mut World) {}

    fn update_archetype_component_access(&mut self, _world: UnsafeWorldCell) {}

    fn check_change_tick(&mut self, _change_tick: Tick) {}

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
        result::Result,
        schedule::default::ScheduledSystem,
        system::ReadOnlySystem,
        world::{unsafe_world_cell::UnsafeWorldCell, World},
    };

    /// # Safety
    /// See `System::run_unsafe`.
    #[inline(never)]
    pub(super) unsafe fn run_unsafe(
        system: &mut ScheduledSystem,
        world: UnsafeWorldCell,
    ) -> Result {
        let result = system.run_unsafe((), world);
        black_box(());
        result
    }

    /// # Safety
    /// See `ReadOnlySystem::run_unsafe`.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    #[inline(never)]
    pub(super) unsafe fn readonly_run_unsafe<O: 'static>(
        system: &mut dyn ReadOnlySystem<In = (), Out = O>,
        world: UnsafeWorldCell,
    ) -> O {
        black_box(system.run_unsafe((), world))
    }

    #[inline(never)]
    pub(super) fn run(system: &mut ScheduledSystem, world: &mut World) -> Result {
        let result = system.run((), world);
        black_box(());
        result
    }

    #[inline(never)]
    pub(super) fn readonly_run<O: 'static>(
        system: &mut dyn ReadOnlySystem<In = (), Out = O>,
        world: &mut World,
    ) -> O {
        black_box(system.run((), world))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        prelude::{Resource, Schedule, SystemSet},
        schedule::{
            default::{
                IntoChainableNodeConfigs, IntoConditionalNodeConfigs, IntoOrderedNodeConfigs,
            },
            ExecutorKind,
        },
        system::{Commands, Res, WithParamWarnPolicy},
        world::World,
    };

    #[derive(Resource)]
    struct R1;

    #[derive(Resource)]
    struct R2;

    const EXECUTORS: [ExecutorKind; 3] = [
        ExecutorKind::Simple,
        ExecutorKind::SingleThreaded,
        ExecutorKind::MultiThreaded,
    ];

    #[test]
    fn invalid_system_param_skips() {
        for executor in EXECUTORS {
            invalid_system_param_skips_core(executor);
        }
    }

    fn invalid_system_param_skips_core(executor: ExecutorKind) {
        let mut world = World::new();
        let mut schedule = Schedule::default();
        schedule.set_executor_kind(executor);
        schedule.add_systems(
            (
                // This system depends on a system that is always skipped.
                (|mut commands: Commands| {
                    commands.insert_resource(R2);
                })
                .warn_param_missing(),
            )
                .chain(),
        );
        schedule.run(&mut world);
        assert!(world.get_resource::<R1>().is_none());
        assert!(world.get_resource::<R2>().is_some());
    }

    #[derive(SystemSet, Hash, Debug, PartialEq, Eq, Clone)]
    struct S1;

    #[test]
    fn invalid_condition_param_skips_system() {
        for executor in EXECUTORS {
            invalid_condition_param_skips_system_core(executor);
        }
    }

    fn invalid_condition_param_skips_system_core(executor: ExecutorKind) {
        let mut world = World::new();
        let mut schedule = Schedule::default();
        schedule.set_executor_kind(executor);
        schedule.configure_sets(S1.run_if((|_: Res<R1>| true).warn_param_missing()));
        schedule.add_systems((
            // System gets skipped if system set run conditions fail validation.
            (|mut commands: Commands| {
                commands.insert_resource(R1);
            })
            .warn_param_missing()
            .in_set(S1),
            // System gets skipped if run conditions fail validation.
            (|mut commands: Commands| {
                commands.insert_resource(R2);
            })
            .warn_param_missing()
            .run_if((|_: Res<R2>| true).warn_param_missing()),
        ));
        schedule.run(&mut world);
        assert!(world.get_resource::<R1>().is_none());
        assert!(world.get_resource::<R2>().is_none());
    }
}
