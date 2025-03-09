use bevy_ecs::schedule::{
    default::DenselyChained,
    graph::Direction,
    traits::{GraphNode, GraphNodeId, ProcessedConfigs},
    FallibleReadOnlySystem, Hierarchy, InternedSystemSet, NodeConfig, NodeConfigs,
};
use fixedbitset::FixedBitSet;

use crate::render_graph2::{
    RenderGraph, RenderGraphError, RenderGroupMetadata, RenderNode, RenderNodeContext,
    RenderNodeMetadata,
};

pub type FallibleRenderSystem = FallibleReadOnlySystem<RenderNodeContext<'static>>;

impl GraphNode<RenderGraph> for FallibleRenderSystem {
    type Metadata = RenderNodeMetadata;
    type GroupMetadata = RenderGroupMetadata;
    type ProcessData = DenselyChained;

    fn into_config(self) -> NodeConfig<Self, RenderGraph> {
        let sets = self.0.default_system_sets();
        NodeConfig {
            node: self,
            metadata: RenderNodeMetadata {
                hierarchy: Hierarchy(sets),
                ..Default::default()
            },
        }
    }

    fn process_config(
        graph: &mut RenderGraph,
        config: NodeConfig<Self, RenderGraph>,
    ) -> Result<RenderNodeId, RenderGraphError> {
        let id = RenderNodeId::System(graph.systems.len());

        graph.update_graphs(id, config.metadata.hierarchy, config.metadata.dependencies)?;

        // system init has to be deferred (need `&mut World`)
        graph.uninit.push(id.index());
        graph.systems.push(RenderNode::new(config.node.0));

        Ok(id)
    }

    fn process_configs(
        graph: &mut RenderGraph,
        configs: NodeConfigs<Self, RenderGraph>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self, RenderGraph>, RenderGraphError> {
        graph.process_configs(configs, collect_nodes)
    }
}

impl GraphNode<RenderGraph> for InternedSystemSet {
    type Metadata = RenderNodeMetadata;
    type GroupMetadata = RenderGroupMetadata;
    type ProcessData = DenselyChained;

    fn into_config(self) -> NodeConfig<Self, RenderGraph> {
        NodeConfig {
            node: self,
            metadata: RenderNodeMetadata::default(),
        }
    }

    fn process_config(
        graph: &mut RenderGraph,
        config: NodeConfig<Self, RenderGraph>,
    ) -> Result<RenderNodeId, RenderGraphError> {
        let id = match graph.system_set_ids.get(&config.node) {
            Some(id) => *id,
            None => graph.add_set(config.node),
        };

        graph.update_graphs(id, config.metadata.hierarchy, config.metadata.dependencies)?;

        Ok(id)
    }

    fn process_configs(
        graph: &mut RenderGraph,
        configs: NodeConfigs<Self, RenderGraph>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self, RenderGraph>, RenderGraphError> {
        graph.process_configs(configs, collect_nodes)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum RenderNodeId {
    /// Identifier for a system.
    System(usize),
    /// Identifier for a system set.
    Set(usize),
}

impl RenderNodeId {
    /// Returns the internal integer value.
    pub const fn index(&self) -> usize {
        match self {
            RenderNodeId::System(index) | RenderNodeId::Set(index) => *index,
        }
    }

    pub const fn is_system(&self) -> bool {
        matches!(self, RenderNodeId::System(_))
    }

    pub const fn is_set(&self) -> bool {
        matches!(self, RenderNodeId::Set(_))
    }
}

impl From<RenderNodeId> for usize {
    fn from(id: RenderNodeId) -> Self {
        id.index()
    }
}

impl GraphNodeId for RenderNodeId {
    type Pair = (Self, Self);
    type Directed = (Self, Direction);
    type Set = FixedBitSet;

    fn kind(&self) -> &'static str {
        match self {
            RenderNodeId::System(_) => "system",
            RenderNodeId::Set(_) => "system set",
        }
    }
}
