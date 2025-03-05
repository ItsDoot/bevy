use bevy_ecs::schedule::{
    default::DenselyChained,
    graph::Direction,
    traits::{GraphNode, GraphNodeId, ProcessedConfigs},
    FallibleReadOnlySystem, NodeConfig, NodeConfigs,
};
use fixedbitset::FixedBitSet;
use wgpu::CommandBuffer;

use crate::render_graph2::{
    RenderCtx, RenderGraph, RenderGraphError, RenderGroupMetadata, RenderNodeMetadata,
};

pub type FallibleRenderSystem = FallibleReadOnlySystem<RenderCtx<'static>, CommandBuffer>;

impl GraphNode<RenderGraph> for FallibleRenderSystem {
    type Metadata = RenderNodeMetadata;
    type GroupMetadata = RenderGroupMetadata;
    type ProcessData = DenselyChained;

    fn into_config(self) -> NodeConfig<Self, RenderGraph> {
        let sets = self.0.default_system_sets();
        NodeConfig {
            node: self,
            metadata: RenderNodeMetadata {
                // TODO
            },
        }
    }

    fn process_config(
        graph: &mut RenderGraph,
        config: NodeConfig<Self, RenderGraph>,
    ) -> Result<RenderNodeId, RenderGraphError> {
        todo!()
    }

    fn process_configs(
        graph: &mut RenderGraph,
        configs: NodeConfigs<Self, RenderGraph>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self, RenderGraph>, RenderGraphError> {
        todo!()
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

    /// Returns the name for the type of node.
    pub fn type_name(&self) -> &'static str {
        match self {
            RenderNodeId::System(_) => "system",
            RenderNodeId::Set(_) => "system set",
        }
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
}
