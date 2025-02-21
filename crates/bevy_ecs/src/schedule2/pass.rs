use alloc::{boxed::Box, vec::Vec};
use core::{
    any::{Any, TypeId},
    fmt::Debug,
};

use bevy_utils::TypeIdMap;

use crate::{
    schedule2::{graph::DiGraph, ScheduleGraph},
    world::World,
};

/// A pass for modular modification of the dependency graph.
pub trait ScheduleBuildPass<G: ScheduleGraph>: Send + Sync + Debug + 'static {
    /// Custom options for dependencies between nodes.
    type EdgeOptions: 'static;

    /// Called when a dependency between nodes was explicitly added to the graph.
    fn add_dependency(&mut self, from: G::Id, to: G::Id, options: Option<&Self::EdgeOptions>);

    /// Called while flattening the dependency graph. For each `set`, this method is called
    /// with the `systems` associated with the set as well as an immutable reference to the current graph.
    /// Instead of modifying the graph directly, this method should return an iterator of edges to add to the graph.
    fn collapse_set(
        &mut self,
        set: G::Id,
        systems: &[G::Id],
        dependency_flattened: &DiGraph<G::Id>,
    ) -> impl Iterator<Item = (G::Id, G::Id)>;

    /// The implementation will be able to modify the `ScheduleGraph` here.
    fn build(
        &mut self,
        world: &mut World,
        graph: &mut G,
        dependency_flattened: &mut DiGraph<G::Id>,
    ) -> Result<(), G::BuildError>;
}

/// Dyn-compatible version of [`ScheduleBuildPass`].
pub(super) trait DynScheduleBuildPass<G: ScheduleGraph>: Send + Sync + Debug {
    fn add_dependency(&mut self, from: G::Id, to: G::Id, all_options: &TypeIdMap<Box<dyn Any>>);

    fn collapse_set(
        &mut self,
        set: G::Id,
        systems: &[G::Id],
        dependency_flattened: &DiGraph<G::Id>,
        dependencies_to_add: &mut Vec<(G::Id, G::Id)>,
    );

    fn build(
        &mut self,
        world: &mut World,
        graph: &mut G,
        dependency_flattened: &mut DiGraph<G::Id>,
    ) -> Result<(), G::BuildError>;
}

impl<T: ScheduleBuildPass<G>, G: ScheduleGraph> DynScheduleBuildPass<G> for T {
    fn add_dependency(&mut self, from: G::Id, to: G::Id, all_options: &TypeIdMap<Box<dyn Any>>) {
        let option = all_options
            .get(&TypeId::of::<T::EdgeOptions>())
            .and_then(|x| x.downcast_ref::<T::EdgeOptions>());
        self.add_dependency(from, to, option);
    }

    fn collapse_set(
        &mut self,
        set: G::Id,
        systems: &[G::Id],
        dependency_flattened: &DiGraph<G::Id>,
        dependencies_to_add: &mut Vec<(G::Id, G::Id)>,
    ) {
        let iter = self.collapse_set(set, systems, dependency_flattened);
        dependencies_to_add.extend(iter);
    }

    fn build(
        &mut self,
        world: &mut World,
        graph: &mut G,
        dependency_flattened: &mut DiGraph<G::Id>,
    ) -> Result<(), G::BuildError> {
        self.build(world, graph, dependency_flattened)
    }
}
