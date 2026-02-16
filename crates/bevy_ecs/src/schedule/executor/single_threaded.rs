use core::panic::AssertUnwindSafe;
use fixedbitset::FixedBitSet;

#[cfg(feature = "trace")]
use alloc::string::ToString as _;
#[cfg(feature = "trace")]
use tracing::info_span;

#[cfg(feature = "std")]
use std::eprintln;

use crate::{
    change_detection::CheckChangeTicks,
    error::{ErrorContext, ErrorHandler, Result},
    schedule::{
        graph::{Dag, DagAnalysis},
        is_apply_deferred, ConditionWithAccess, ExecutorKind, NodeId, ScheduleGraph,
        ScheduleNotInitialized, SystemExecutor, SystemKey, SystemSchedule,
    },
    system::{RunSystemError, ScheduleSystem},
    world::World,
};

#[cfg(feature = "hotpatching")]
use crate::{change_detection::DetectChanges, HotPatchChanges};

use super::__rust_begin_short_backtrace;

/// Runs the schedule using a single thread.
///
/// Useful if you're dealing with a single-threaded environment, saving your threads for
/// other things, or just trying minimize overhead.
#[derive(Default)]
pub struct SingleThreadedExecutor {
    executable: Option<SystemSchedule>,
    /// System sets whose conditions have been evaluated.
    evaluated_sets: FixedBitSet,
    /// Systems that have run or been skipped.
    completed_systems: FixedBitSet,
    /// Systems that have run but have not had their buffers applied.
    unapplied_systems: FixedBitSet,
    /// Setting when true applies deferred system buffers after all systems have run
    apply_final_deferred: bool,
}

impl SystemExecutor for SingleThreadedExecutor {
    fn kind(&self) -> ExecutorKind {
        ExecutorKind::SingleThreaded
    }

    fn is_initialized(&self) -> bool {
        self.executable.is_some()
    }

    fn initialize(
        &mut self,
        graph: &ScheduleGraph,
        flat_dependency: &Dag<SystemKey>,
        hierarchy_analysis: &DagAnalysis<NodeId>,
    ) {
        let (executable, _) = SystemSchedule::new(graph, flat_dependency, hierarchy_analysis);

        // pre-allocate space
        let sys_count = executable.system_ids.len();
        let set_count = executable.set_ids.len();
        self.evaluated_sets = FixedBitSet::with_capacity(set_count);
        self.completed_systems = FixedBitSet::with_capacity(sys_count);
        self.unapplied_systems = FixedBitSet::with_capacity(sys_count);

        self.executable = Some(executable);
    }

    fn run(
        &mut self,
        world: &mut World,
        _skip_systems: Option<&FixedBitSet>,
        error_handler: ErrorHandler,
    ) -> Result<(), ScheduleNotInitialized> {
        // If stepping is enabled, make sure we skip those systems that should
        // not be run.
        #[cfg(feature = "bevy_debug_stepping")]
        if let Some(skipped_systems) = _skip_systems {
            // mark skipped systems as completed
            self.completed_systems |= skipped_systems;
        }

        #[cfg(feature = "hotpatching")]
        let hotpatch_tick = world
            .get_resource_ref::<HotPatchChanges>()
            .map(|r| r.last_changed())
            .unwrap_or_default();

        let executable = self.executable.as_mut().ok_or(ScheduleNotInitialized)?;

        for system_index in 0..executable.systems.len() {
            let system = &mut executable.systems[system_index].system;

            #[cfg(feature = "trace")]
            let name = system.lock().name();
            #[cfg(feature = "trace")]
            let should_run_span = info_span!("check_conditions", name = name.to_string()).entered();

            let mut should_run = !self.completed_systems.contains(system_index);
            for set_idx in executable.sets_with_conditions_of_systems[system_index].ones() {
                if self.evaluated_sets.contains(set_idx) {
                    continue;
                }

                // evaluate system set's conditions
                let set_conditions_met = evaluate_and_fold_conditions(
                    &mut executable.set_conditions[set_idx],
                    world,
                    error_handler,
                    system,
                    true,
                );

                if !set_conditions_met {
                    self.completed_systems
                        .union_with(&executable.systems_in_sets_with_conditions[set_idx]);
                }

                should_run &= set_conditions_met;
                self.evaluated_sets.insert(set_idx);
            }

            // evaluate system's conditions
            let system_conditions_met = evaluate_and_fold_conditions(
                &mut executable.system_conditions[system_index],
                world,
                error_handler,
                system,
                false,
            );

            should_run &= system_conditions_met;

            #[cfg(feature = "trace")]
            should_run_span.exit();

            #[cfg(feature = "hotpatching")]
            if hotpatch_tick.is_newer_than(system.get_last_run(), world.change_tick()) {
                system.refresh_hotpatch();
            }

            // system has either been skipped or will run
            self.completed_systems.insert(system_index);

            if !should_run {
                continue;
            }

            if is_apply_deferred(&*system.lock()) {
                for system_index in self.unapplied_systems.ones() {
                    executable.systems[system_index]
                        .system
                        .lock()
                        .apply_deferred(world);
                }
                self.unapplied_systems.clear();
                continue;
            }

            let f = AssertUnwindSafe(|| {
                if let Err(RunSystemError::Failed(err)) =
                    __rust_begin_short_backtrace::run_without_applying_deferred(
                        &mut *system.lock(),
                        world,
                    )
                {
                    error_handler(
                        err,
                        ErrorContext::System {
                            name: system.lock().name(),
                            last_run: system.lock().get_last_run(),
                        },
                    );
                }
            });

            #[cfg(feature = "std")]
            #[expect(clippy::print_stderr, reason = "Allowed behind `std` feature gate.")]
            {
                if let Err(payload) = std::panic::catch_unwind(f) {
                    eprintln!("Encountered a panic in system `{}`!", system.lock().name());
                    std::panic::resume_unwind(payload);
                }
            }

            #[cfg(not(feature = "std"))]
            {
                (f)();
            }

            self.unapplied_systems.insert(system_index);
        }

        if self.apply_final_deferred {
            self.apply_deferred(world);
        }
        self.evaluated_sets.clear();
        self.completed_systems.clear();
        Ok(())
    }

    fn set_apply_final_deferred(&mut self, apply_final_deferred: bool) {
        self.apply_final_deferred = apply_final_deferred;
    }

    fn check_change_ticks(&mut self, check: CheckChangeTicks) {
        if let Some(executable) = &mut self.executable {
            for system in &mut executable.systems {
                let mut system = system.lock();
                if !is_apply_deferred(&*system) {
                    system.check_change_tick(check);
                }
            }

            for conditions in &mut executable.system_conditions {
                for condition in conditions {
                    condition.lock().check_change_tick(check);
                }
            }

            for conditions in &mut executable.set_conditions {
                for condition in conditions {
                    condition.lock().check_change_tick(check);
                }
            }
        }
    }

    fn apply_deferred(&mut self, world: &mut World) {
        if let Some(executable) = &mut self.executable {
            for system_index in self.unapplied_systems.ones() {
                executable.systems[system_index]
                    .system
                    .lock()
                    .apply_deferred(world);
            }
            self.unapplied_systems.clear();
        }
    }
}

impl SingleThreadedExecutor {
    /// Creates a new single-threaded executor for use in a [`Schedule`].
    ///
    /// [`Schedule`]: crate::schedule::Schedule
    pub const fn new() -> Self {
        Self {
            executable: None,
            evaluated_sets: FixedBitSet::new(),
            completed_systems: FixedBitSet::new(),
            unapplied_systems: FixedBitSet::new(),
            apply_final_deferred: true,
        }
    }
}

fn evaluate_and_fold_conditions(
    conditions: &mut [ConditionWithAccess],
    world: &mut World,
    error_handler: ErrorHandler,
    for_system: &ScheduleSystem,
    on_set: bool,
) -> bool {
    #[cfg(feature = "hotpatching")]
    let hotpatch_tick = world
        .get_resource_ref::<HotPatchChanges>()
        .map(|r| r.last_changed())
        .unwrap_or_default();

    #[expect(
        clippy::unnecessary_fold,
        reason = "Short-circuiting here would prevent conditions from mutating their own state as needed."
    )]
    conditions
        .iter_mut()
        .map(|condition| {
            let mut condition = condition.lock();
            #[cfg(feature = "hotpatching")]
            if hotpatch_tick.is_newer_than(condition.get_last_run(), world.change_tick()) {
                condition.refresh_hotpatch();
            }
            __rust_begin_short_backtrace::readonly_run(&mut *condition, world).unwrap_or_else(
                |err| {
                    if let RunSystemError::Failed(err) = err {
                        error_handler(
                            err,
                            ErrorContext::RunCondition {
                                name: condition.name(),
                                last_run: condition.get_last_run(),
                                system: for_system.lock().name(),
                                on_set,
                            },
                        );
                    };
                    false
                },
            )
        })
        .fold(true, |acc, res| acc && res)
}
