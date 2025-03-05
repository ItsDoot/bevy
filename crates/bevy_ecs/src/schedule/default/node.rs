use core::fmt::{self, Debug};

use fixedbitset::FixedBitSet;

use crate::{
    prelude::SystemSet,
    result::Result,
    schedule::{
        default::{
            DefaultBuildError, DefaultGraph, DefaultGroupMetadata, DefaultMetadata, GraphInfo,
        },
        graph::Direction,
        traits::{DirectedGraphNodeId, GraphNode, GraphNodeId, GraphNodeIdPair, ProcessedConfigs},
        Conditions, FallibleSystem, Hierarchy, InternedSystemSet, NodeConfig, NodeConfigs,
    },
    system::BoxedSystem,
};

/// [`DefaultGraph`] [`GraphNode`] for inserting systems into the schedule.
pub type ScheduledSystem<In = (), Out = ()> = BoxedSystem<In, Result<Out>>;

/// Shorthand for [`NodeConfigs`] containing [`ScheduledSystem`]s.
pub type SystemConfigs<In = (), Out = (), G = DefaultGraph> =
    NodeConfigs<FallibleSystem<In, Out>, G>;

impl GraphNode<DefaultGraph> for FallibleSystem {
    type Metadata = DefaultMetadata;
    type GroupMetadata = DefaultGroupMetadata;
    type ProcessData = DenselyChained;

    fn into_config(self) -> NodeConfig<Self, DefaultGraph> {
        // include system in its default sets
        let sets = self.0.default_system_sets();
        NodeConfig {
            node: self,
            metadata: DefaultMetadata {
                graph_info: GraphInfo {
                    hierarchy: Hierarchy(sets),
                    ..Default::default()
                },
                conditions: Conditions::default(),
            },
        }
    }

    fn process_config(
        graph: &mut DefaultGraph,
        config: NodeConfig<Self, DefaultGraph>,
    ) -> Result<NodeId, DefaultBuildError> {
        graph.add_system_inner(config)
    }

    fn process_configs(
        graph: &mut DefaultGraph,
        configs: NodeConfigs<Self, DefaultGraph>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self, DefaultGraph>, DefaultBuildError> {
        graph.process_configs(configs, collect_nodes)
    }
}

/// Shorthand for [`NodeConfigs`] containing [`InternedSystemSet`]s.
pub type SystemSetConfigs<G = DefaultGraph> = NodeConfigs<InternedSystemSet, G>;

impl GraphNode<DefaultGraph> for InternedSystemSet {
    type Metadata = DefaultMetadata;
    type GroupMetadata = DefaultGroupMetadata;
    type ProcessData = DenselyChained;

    fn into_config(self) -> NodeConfig<Self, DefaultGraph> {
        // system type sets are automatically populated
        // to avoid unintentionally broad changes, they cannot be configured
        assert!(
            self.system_type().is_none(),
            "configuring system type sets is not allowed"
        );

        NodeConfig {
            node: self,
            metadata: DefaultMetadata::default(),
        }
    }

    fn process_config(
        graph: &mut DefaultGraph,
        config: NodeConfig<Self, DefaultGraph>,
    ) -> Result<NodeId, DefaultBuildError> {
        graph.configure_set_inner(config)
    }

    fn process_configs(
        graph: &mut DefaultGraph,
        configs: NodeConfigs<Self, DefaultGraph>,
        collect_nodes: bool,
    ) -> Result<ProcessedConfigs<Self, DefaultGraph>, DefaultBuildError> {
        graph.process_configs(configs, collect_nodes)
    }
}

/// Unique identifier for a system or system set stored in a [`DefaultGraph`].
///
/// [`DefaultGraph`]: crate::schedule::default::DefaultGraph
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NodeId {
    /// Identifier for a system.
    System(usize),
    /// Identifier for a system set.
    Set(usize),
}

impl NodeId {
    /// Returns the internal integer value.
    pub const fn index(&self) -> usize {
        match self {
            NodeId::System(index) | NodeId::Set(index) => *index,
        }
    }

    /// Returns `true` if the identified node is a system.
    pub const fn is_system(&self) -> bool {
        matches!(self, NodeId::System(_))
    }

    /// Returns `true` if the identified node is a system set.
    pub const fn is_set(&self) -> bool {
        matches!(self, NodeId::Set(_))
    }

    /// Compare this [`NodeId`] with another.
    pub const fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        use core::cmp::Ordering::{Equal, Greater, Less};
        use NodeId::{Set, System};

        match (self, other) {
            (System(a), System(b)) | (Set(a), Set(b)) => match a.checked_sub(*b) {
                None => Less,
                Some(0) => Equal,
                Some(_) => Greater,
            },
            (System(_), Set(_)) => Less,
            (Set(_), System(_)) => Greater,
        }
    }
}

impl From<NodeId> for usize {
    fn from(id: NodeId) -> Self {
        id.index()
    }
}

impl GraphNodeId for NodeId {
    type Pair = CompactNodeIdPair;
    type Directed = CompactNodeIdAndDirection;
    type Set = FixedBitSet;
}

/// Compact storage of a [`NodeId`] and a [`Direction`].
#[derive(Clone, Copy)]
pub struct CompactNodeIdAndDirection {
    index: usize,
    is_system: bool,
    direction: Direction,
}

impl DirectedGraphNodeId<NodeId> for CompactNodeIdAndDirection {
    fn new(node: NodeId, direction: Direction) -> Self {
        let (index, is_system) = match node {
            NodeId::System(index) => (index, true),
            NodeId::Set(index) => (index, false),
        };

        Self {
            index,
            is_system,
            direction,
        }
    }

    fn unpack(self) -> (NodeId, Direction) {
        let Self {
            index,
            is_system,
            direction,
        } = self;

        let node = match is_system {
            true => NodeId::System(index),
            false => NodeId::Set(index),
        };

        (node, direction)
    }
}

impl Debug for CompactNodeIdAndDirection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.unpack().fmt(f)
    }
}

/// Compact storage of a [`NodeId`] pair.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct CompactNodeIdPair {
    index_a: usize,
    index_b: usize,
    is_system_a: bool,
    is_system_b: bool,
}

impl GraphNodeIdPair<NodeId> for CompactNodeIdPair {
    fn new(a: NodeId, b: NodeId) -> Self {
        Self {
            index_a: a.index(),
            is_system_a: a.is_system(),
            index_b: b.index(),
            is_system_b: b.is_system(),
        }
    }

    fn unpack(self) -> (NodeId, NodeId) {
        (
            match self.is_system_a {
                true => NodeId::System(self.index_a),
                false => NodeId::Set(self.index_a),
            },
            match self.is_system_b {
                true => NodeId::System(self.index_b),
                false => NodeId::Set(self.index_b),
            },
        )
    }
}

impl Debug for CompactNodeIdPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.unpack().fmt(f)
    }
}

/// Metadata returned by [`GraphNode`]s when processing a group of nodes.
pub struct DenselyChained(pub bool);
