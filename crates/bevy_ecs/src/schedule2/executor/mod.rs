use crate::{
    result::{Error, SystemErrorContext},
    schedule2::ScheduleGraph,
    world::World,
};

mod simple;

pub use self::simple::*;

/// Types that can run a [`ScheduleGraph::Executable`] on a [`World`].
pub trait ScheduleExecutor<G: ScheduleGraph>: Send + Sync + 'static {
    /// The kind of executor.
    fn kind(&self) -> G::ExecutorKind;

    /// Initializes the executor for the given executable.
    fn initialize(&mut self, executable: &G::Executable);

    // TODO: add skip_systems argument
    /// Runs the executable on the world.
    fn run(
        &mut self,
        executable: &mut G::Executable,
        world: &mut World,
        error_handler: fn(Error, SystemErrorContext),
    );

    /// Sets whether commands from systems should be applied at the end of the run.
    fn set_apply_final_deferred(&mut self, value: bool);
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
        system::{ReadOnlySystem, ScheduleSystem},
        world::{unsafe_world_cell::UnsafeWorldCell, World},
    };

    /// # Safety
    /// See `System::run_unsafe`.
    #[inline(never)]
    pub(super) unsafe fn run_unsafe(system: &mut ScheduleSystem, world: UnsafeWorldCell) -> Result {
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
    pub(super) fn run(system: &mut ScheduleSystem, world: &mut World) -> Result {
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
