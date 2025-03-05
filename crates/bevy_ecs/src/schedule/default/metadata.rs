use crate::schedule::{Ambiguities, Chain, Conditions, Dependencies, Hierarchy, InternedSystemSet};

/// Metadata for a single node in the [`DefaultGraph`](crate::schedule::default::DefaultGraph).
#[derive(Default)]
pub struct DefaultMetadata {
    /// Hierarchy and dependency metadata for this node
    pub(crate) graph_info: GraphInfo,
    /// Conditions required for this node to run.
    pub(crate) conditions: Conditions,
}

impl AsMut<Hierarchy<InternedSystemSet>> for DefaultMetadata {
    fn as_mut(&mut self) -> &mut Hierarchy<InternedSystemSet> {
        &mut self.graph_info.hierarchy
    }
}

impl AsMut<Dependencies<InternedSystemSet>> for DefaultMetadata {
    fn as_mut(&mut self) -> &mut Dependencies<InternedSystemSet> {
        &mut self.graph_info.dependencies
    }
}

impl AsMut<Ambiguities<InternedSystemSet>> for DefaultMetadata {
    fn as_mut(&mut self) -> &mut Ambiguities<InternedSystemSet> {
        &mut self.graph_info.ambiguous_with
    }
}

impl AsMut<Conditions> for DefaultMetadata {
    fn as_mut(&mut self) -> &mut Conditions {
        &mut self.conditions
    }
}

/// Metadata about how the node fits in the schedule graph
#[derive(Default)]
pub struct GraphInfo {
    /// the sets that the node belongs to (hierarchy)
    pub(crate) hierarchy: Hierarchy<InternedSystemSet>,
    /// the sets that the node depends on (must run before or after)
    pub(crate) dependencies: Dependencies<InternedSystemSet>,
    pub(crate) ambiguous_with: Ambiguities<InternedSystemSet>,
}

/// Metadata for a group of nodes in the [`DefaultGraph`](crate::schedule::default::DefaultGraph).
#[derive(Default)]
pub struct DefaultGroupMetadata {
    /// Run conditions applied to everything in the tuple.
    pub collective_conditions: Conditions,
    /// See [`Chain`] for usage.
    pub chained: Chain,
}

impl AsMut<Conditions> for DefaultGroupMetadata {
    fn as_mut(&mut self) -> &mut Conditions {
        &mut self.collective_conditions
    }
}

impl AsMut<Chain> for DefaultGroupMetadata {
    fn as_mut(&mut self) -> &mut Chain {
        &mut self.chained
    }
}
