//! Traits used to define custom schedule graphs.

use core::{fmt::Debug, hash::Hash};

use crate::schedule::graph::Direction;

/// Trait for types that can be used as unique identifiers in a [`DiGraph`] or
/// [`UnGraph`].
///
/// [`DiGraph`]: crate::schedule::graph::DiGraph
/// [`UnGraph`]: crate::schedule::graph::UnGraph
pub trait GraphNodeId: Copy + Eq + Ord + Hash + Debug + 'static {
    /// The type of pair of identifiers used to represent an edge in the graph.
    type Pair: GraphNodeIdPair<Self>;
    /// The type of directed identifier used to represent a directed edge in the graph.
    type Directed: DirectedGraphNodeId<Self>;
}

/// Trait for types that hold a pair of [`GraphNodeId`]s. Typically stored in a
/// memory-efficient way.
pub trait GraphNodeIdPair<Id: GraphNodeId>: Copy + Eq + Hash {
    /// Creates a new pair of identifiers.
    fn new(a: Id, b: Id) -> Self;

    /// Unpacks the pair into its components.
    fn unpack(self) -> (Id, Id);
}

/// Trait for types that hold a [`GraphNodeId`] and a [`Direction`]. Typically
/// stored in a memory-efficient way.
pub trait DirectedGraphNodeId<Id: GraphNodeId>: Copy + Debug {
    /// Creates a new directed identifier.
    fn new(node: Id, direction: Direction) -> Self;

    /// Unpacks the directed identifier into its components.
    fn unpack(self) -> (Id, Direction);
}
