use alloc::boxed::Box;
use core::any::{Any, TypeId};

use bevy_utils::TypeIdMap;

use crate::{
    prelude::IntoNodeConfigs,
    schedule::{
        passes::IgnoreDeferred,
        traits::{GraphNode, ScheduleGraph},
        NodeConfigs,
    },
};

/// Chain systems into dependencies
#[derive(Default)]
pub enum Chain {
    /// Systems are independent. Nodes are allowed to run in any order.
    #[default]
    Unchained,
    /// Systems are chained. `before -> after` ordering constraints
    /// will be added between the successive elements.
    Chained(TypeIdMap<Box<dyn Any>>),
}

impl Chain {
    /// Specify that the systems must be chained.
    pub fn set_chained(&mut self) {
        if matches!(self, Chain::Unchained) {
            *self = Self::Chained(Default::default());
        };
    }
    /// Specify that the systems must be chained, and add the specified configuration for
    /// all dependencies created between these systems.
    pub fn set_chained_with_config<T: 'static>(&mut self, config: T) {
        self.set_chained();
        if let Chain::Chained(config_map) = self {
            config_map.insert(TypeId::of::<T>(), Box::new(config));
        } else {
            unreachable!()
        };
    }
}

impl AsRef<Self> for Chain {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl AsMut<Self> for Chain {
    fn as_mut(&mut self) -> &mut Chain {
        self
    }
}

impl<N: GraphNode<G, GroupMetadata: AsMut<Chain>>, G: ScheduleGraph> NodeConfigs<N, G> {
    /// Chain these nodes together in a sequence.
    pub fn chain_inner(&mut self) {
        match self {
            Self::Single(_) => { /* no op */ }
            Self::Group { metadata, .. } => {
                metadata.as_mut().set_chained();
            }
        };
    }

    /// Chain these nodes together in a sequence, but do not add
    /// [`ApplyDeferred`](crate::schedule::ApplyDeferred) on the edges.
    pub fn chain_ignore_deferred_inner(&mut self) {
        match self {
            Self::Single(_) => { /* no op */ }
            Self::Group { metadata, .. } => {
                metadata.as_mut().set_chained_with_config(IgnoreDeferred);
            }
        };
    }
}

/// [`GraphNode`]s that can be configured to run in a specific order, chained together in a group.
pub trait IntoChainableNodeConfigs<N, G, Marker>: IntoNodeConfigs<N, G, Marker>
where
    N: GraphNode<G, GroupMetadata: AsMut<Chain>>,
    G: ScheduleGraph,
{
    /// Treat this collection as a sequence of systems.
    ///
    /// Ordering constraints will be applied between the successive elements.
    ///
    /// If the preceding node on an edge has deferred parameters, an [`ApplyDeferred`](crate::schedule::ApplyDeferred)
    /// will be inserted on the edge. If this behavior is not desired consider using
    /// [`chain_ignore_deferred`](Self::chain_ignore_deferred) instead.
    fn chain(self) -> NodeConfigs<N, G> {
        let mut configs = self.into_configs();
        configs.chain_inner();
        configs
    }

    /// Treat this collection as a sequence of systems.
    ///
    /// Ordering constraints will be applied between the successive elements.
    ///
    /// Unlike [`chain`](Self::chain) this will **not** add [`ApplyDeferred`](crate::schedule::ApplyDeferred) on the edges.
    fn chain_ignore_deferred(self) -> NodeConfigs<N, G> {
        let mut configs = self.into_configs();
        configs.chain_ignore_deferred_inner();
        configs
    }
}

impl<N, G, M, I> IntoChainableNodeConfigs<N, G, M> for I
where
    N: GraphNode<G, GroupMetadata: AsMut<Chain>>,
    G: ScheduleGraph,
    I: IntoNodeConfigs<N, G, M>,
{
}
