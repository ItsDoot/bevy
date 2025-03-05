use alloc::vec::Vec;
use derive_more::derive::{Deref, DerefMut};

use crate::{
    prelude::{IntoNodeConfigs, SystemSet},
    schedule::{
        traits::{GraphNode, ScheduleGraph},
        InternedSystemSet, NodeConfigs,
    },
};

/// Metadata that specifies a [`GraphNode`] belongs to a specific group.
///
/// [`GraphNode`]: crate::schedule::traits::GraphNode
#[derive(Deref, DerefMut)]
pub struct Hierarchy<T>(pub Vec<T>);

impl<T> Default for Hierarchy<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> AsRef<Self> for Hierarchy<T> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T> AsMut<Self> for Hierarchy<T> {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<N: GraphNode<G>, G: ScheduleGraph> NodeConfigs<N, G> {
    /// Adds these nodes to the specified set.
    pub fn in_set_inner<T: Clone>(&mut self, set: T)
    where
        N::Metadata: AsMut<Hierarchy<T>>,
    {
        match self {
            Self::Single(config) => {
                config.metadata.as_mut().push(set);
            }
            Self::Group { configs, .. } => {
                for config in configs {
                    config.in_set_inner(set.clone());
                }
            }
        }
    }
}

/// Types that can be converted into [`NodeConfigs`] with [`SystemSet`]
/// hierarchy metadata.
pub trait IntoHierarchicalNodeConfigs<N, G, Marker>: IntoNodeConfigs<N, G, Marker>
where
    N: GraphNode<G, Metadata: AsMut<Hierarchy<InternedSystemSet>>>,
    G: ScheduleGraph,
{
    /// Add these systems to the provided `set`.
    #[track_caller]
    fn in_set(self, set: impl SystemSet) -> NodeConfigs<N, G> {
        assert!(
            set.system_type().is_none(),
            "adding arbitrary systems to a system type set is not allowed"
        );

        let mut configs = self.into_configs();
        configs.in_set_inner(set.intern());
        configs
    }
}

impl<N, G, Marker, I> IntoHierarchicalNodeConfigs<N, G, Marker> for I
where
    N: GraphNode<G, Metadata: AsMut<Hierarchy<InternedSystemSet>>>,
    G: ScheduleGraph,
    I: IntoNodeConfigs<N, G, Marker>,
{
}
