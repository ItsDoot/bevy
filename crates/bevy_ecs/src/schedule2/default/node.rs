use alloc::boxed::Box;

use crate::{
    result::Result,
    schedule::{InternedSystemSet, ScheduleBuildError},
    schedule2::{
        Chain, Conditions, DefaultGraph, GraphInfo, GraphNode, GraphNodeId, IntoNodeConfigs,
        NodeConfig, NodeConfigs, ProcessedConfigs,
    },
    system::{BoxedSystem, InfallibleSystemWrapper, IntoSystem},
};

/// Unique identifier for a system or system set stored in a [`SystemGraph`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum NodeId {
    /// Identifier for a system.
    System(usize),
    /// Identifier for a system set.
    Set(usize),
}

impl NodeId {
    /// Returns `true` if this identifier refers to a system.
    pub fn is_system(&self) -> bool {
        matches!(self, NodeId::System(_))
    }

    /// Returns `true` if this identifier refers to a system set.
    pub fn is_set(&self) -> bool {
        matches!(self, NodeId::Set(_))
    }
}

impl GraphNodeId for NodeId {
    fn index(&self) -> usize {
        match *self {
            NodeId::System(index) | NodeId::Set(index) => index,
        }
    }
}

/// A [`GraphNode`] in a [`SystemGraph`] that represents a system.
#[repr(transparent)]
pub struct ScheduleSystem(pub(crate) BoxedSystem<(), Result>);

impl GraphNode for ScheduleSystem {
    type Metadata = NodeMetadata;
    type GroupMetadata = NodeGroupMetadata;
    type ProcessData = DenselyChained;
    type Graph = DefaultGraph;

    fn into_config(self) -> NodeConfig<Self> {
        let sets = self.0.default_system_sets().clone();
        NodeConfig {
            node: self,
            metadata: NodeMetadata {
                graph_info: GraphInfo {
                    hierarchy: sets,
                    ..GraphInfo::default()
                },
                conditions: Conditions::default(),
            },
        }
    }

    fn process_config(
        graph: &mut DefaultGraph,
        config: NodeConfig<Self>,
    ) -> Result<NodeId, ScheduleBuildError> {
        graph.add_system_inner(config)
    }

    fn process_configs(
        graph: &mut DefaultGraph,
        configs: NodeConfigs<Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self>, ScheduleBuildError> {
        graph.process_configs(configs, collect_nodes)
    }
}

/// A [`GraphNode`] in a [`SystemGraph`] that represents a system set.
#[repr(transparent)]
pub struct ScheduleSystemSet(pub(crate) InternedSystemSet);

impl GraphNode for ScheduleSystemSet {
    type Metadata = NodeMetadata;
    type GroupMetadata = NodeGroupMetadata;
    type ProcessData = DenselyChained;
    type Graph = DefaultGraph;

    fn into_config(self) -> NodeConfig<Self> {
        // system type sets are automatically populated
        // to avoid unintentionally broad changes, they cannot be configured
        assert!(
            self.0.system_type().is_none(),
            "configuring system type sets is not allowed"
        );

        NodeConfig {
            node: self,
            metadata: NodeMetadata::default(),
        }
    }

    fn process_config(
        graph: &mut DefaultGraph,
        config: NodeConfig<Self>,
    ) -> Result<NodeId, ScheduleBuildError> {
        graph.configure_set_inner(config)
    }

    fn process_configs(
        graph: &mut DefaultGraph,
        configs: NodeConfigs<Self>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self>, ScheduleBuildError> {
        graph.process_configs(configs, collect_nodes)
    }
}

/// Stores whether a group of nodes are densely chained.
pub struct DenselyChained(pub(crate) bool);

/// Metadata for [`ScheduleSystem`] and [`ScheduleSystemSet`] nodes.
#[derive(Default)]
pub struct NodeMetadata {
    /// Hierarchy and dependency metadata for this node.
    pub graph_info: GraphInfo,
    /// Conditions for this node to be able to run.
    pub conditions: Conditions,
}

impl AsMut<GraphInfo> for NodeMetadata {
    fn as_mut(&mut self) -> &mut GraphInfo {
        &mut self.graph_info
    }
}

impl AsMut<Conditions> for NodeMetadata {
    fn as_mut(&mut self) -> &mut Conditions {
        &mut self.conditions
    }
}

/// Metadata for groups of [`ScheduleSystem`] and [`ScheduleSystemSet`] nodes.
#[derive(Default)]
pub struct NodeGroupMetadata {
    /// Ordering metadata for this group of nodes.
    pub chain: Chain,
    /// Conditions for this group of nodes to be able to run.
    pub collective_conditions: Conditions,
}

impl AsMut<Chain> for NodeGroupMetadata {
    fn as_mut(&mut self) -> &mut Chain {
        &mut self.chain
    }
}

impl AsMut<Conditions> for NodeGroupMetadata {
    fn as_mut(&mut self) -> &mut Conditions {
        &mut self.collective_conditions
    }
}

/// Marker component to allow for conflicting implementations of [`IntoNodeConfigs`]
#[doc(hidden)]
pub struct Infallible;

impl<F, Marker> IntoNodeConfigs<ScheduleSystem, (Infallible, Marker)> for F
where
    F: IntoSystem<(), (), Marker>,
{
    fn into_configs(self) -> NodeConfigs<ScheduleSystem> {
        let wrapper = InfallibleSystemWrapper::new(IntoSystem::into_system(self));
        NodeConfigs::Single(ScheduleSystem(Box::new(wrapper)).into_config())
    }
}

/// Marker component to allow for conflicting implementations of [`IntoNodeConfigs`]
#[doc(hidden)]
pub struct Fallible;

impl<F, Marker> IntoNodeConfigs<ScheduleSystem, (Fallible, Marker)> for F
where
    F: IntoSystem<(), Result, Marker>,
{
    fn into_configs(self) -> NodeConfigs<ScheduleSystem> {
        let boxed_system = Box::new(IntoSystem::into_system(self));
        NodeConfigs::Single(ScheduleSystem(boxed_system).into_config())
    }
}

impl IntoNodeConfigs<ScheduleSystem, ()> for BoxedSystem<(), Result> {
    fn into_configs(self) -> NodeConfigs<ScheduleSystem> {
        NodeConfigs::Single(ScheduleSystem(self).into_config())
    }
}
