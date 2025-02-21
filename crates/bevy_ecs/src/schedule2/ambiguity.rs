use alloc::{collections::BTreeSet, string::ToString};
use core::{
    borrow::{Borrow, BorrowMut},
    fmt::Write as _,
};

use derive_more::derive::{Deref, DerefMut};
use log::info;

use crate::{
    component::{Component, ComponentId, Components},
    resource::Resource,
    schedule2::{ScheduleGraph, Schedules},
    world::World,
};

/// List of [`ComponentId`]s to ignore when reporting system order ambiguity conflicts
#[derive(Deref, DerefMut, Clone, Default)]
pub struct IgnoredSchedulingAmbiguities(BTreeSet<ComponentId>);

impl<G> Schedules<G>
where
    G: ScheduleGraph,
    G::GlobalMetadata: BorrowMut<IgnoredSchedulingAmbiguities>,
{
    /// Ignore system order ambiguities caused by conflicts on [`Component`]s of type `T`.
    pub fn allow_ambiguous_component<T: Component>(&mut self, world: &mut World) {
        let set: &mut IgnoredSchedulingAmbiguities = self.metadata.borrow_mut();

        set.insert(world.register_component::<T>());
    }

    /// Ignore system order ambiguities caused by conflicts on [`Resource`]s of type `T`.
    pub fn allow_ambiguous_resource<T: Resource>(&mut self, world: &mut World) {
        let set: &mut IgnoredSchedulingAmbiguities = self.metadata.borrow_mut();

        set.insert(world.components.register_resource::<T>());
    }

    /// Iterate through the [`ComponentId`]'s that will be ignored.
    pub fn iter_ignored_ambiguities(&self) -> impl Iterator<Item = &ComponentId> + '_ {
        let set: &IgnoredSchedulingAmbiguities = self.metadata.borrow();

        set.iter()
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
            writeln!(message, "- {}", components.get_name(*id).unwrap()).unwrap();
        }

        info!("{}", message);
    }
}
