use alloc::vec::Vec;
use fixedbitset::FixedBitSet;

use crate::{
    component::Tick,
    schedule::{
        default::{NodeId, ScheduledSystem},
        is_apply_deferred,
        traits::ScheduleExecutable,
        BoxedCondition,
    },
    world::World,
};

/// Holds systems and conditions of a [`Schedule`](crate::schedule::Schedule) sorted in topological order
/// (along with dependency information for `multi_threaded` execution).
///
/// Since the arrays are sorted in the same order, elements are referenced by their index.
/// [`FixedBitSet`] is used as a smaller, more efficient substitute of `HashSet<usize>`.
#[derive(Default)]
pub struct DefaultGraphExecutable {
    /// List of system node ids.
    pub(crate) system_ids: Vec<NodeId>,
    /// Indexed by system node id.
    pub(crate) systems: Vec<ScheduledSystem>,
    /// Indexed by system node id.
    pub(crate) system_conditions: Vec<Vec<BoxedCondition>>,
    /// Indexed by system node id.
    /// Number of systems that the system immediately depends on.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    pub(crate) system_dependencies: Vec<usize>,
    /// Indexed by system node id.
    /// List of systems that immediately depend on the system.
    #[cfg_attr(
        not(feature = "std"),
        expect(dead_code, reason = "currently only used with the std feature")
    )]
    pub(crate) system_dependents: Vec<Vec<usize>>,
    /// Indexed by system node id.
    /// List of sets containing the system that have conditions
    pub(crate) sets_with_conditions_of_systems: Vec<FixedBitSet>,
    /// List of system set node ids.
    pub(crate) set_ids: Vec<NodeId>,
    /// Indexed by system set node id.
    pub(crate) set_conditions: Vec<Vec<BoxedCondition>>,
    /// Indexed by system set node id.
    /// List of systems that are in sets that have conditions.
    ///
    /// If a set doesn't run because of its conditions, this is used to skip all systems in it.
    pub(crate) systems_in_sets_with_conditions: Vec<FixedBitSet>,
}

impl ScheduleExecutable for DefaultGraphExecutable {
    fn apply_deferred(&mut self, world: &mut World) {
        for system in &mut self.systems {
            system.apply_deferred(world);
        }
    }

    fn check_change_ticks(&mut self, change_tick: Tick) {
        for system in &mut self.systems {
            if !is_apply_deferred(system) {
                system.check_change_tick(change_tick);
            }
        }

        for conditions in &mut self.system_conditions {
            for system in conditions {
                system.check_change_tick(change_tick);
            }
        }

        for conditions in &mut self.set_conditions {
            for system in conditions {
                system.check_change_tick(change_tick);
            }
        }
    }
}
