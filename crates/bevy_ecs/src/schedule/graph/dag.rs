use core::ops::Deref;

use alloc::vec::Vec;
use bevy_platform::collections::{HashMap, HashSet};
use fixedbitset::FixedBitSet;

use crate::schedule::graph::{
    graph_map::GraphToposortError,
    DiGraph,
    Direction::{Incoming, Outgoing},
    GraphNodeId,
};

/// A directed acyclic graph (DAG) that caches its topological sort.
///
/// The type parameter `T` is used to statically differentiate between different
/// kinds of graphs (e.g., hierarchy, dependency). The graph is made up of
/// [`GraphNodeId`]s of type `N`.
pub struct Dag<N: GraphNodeId> {
    /// A directed graph.
    graph: DiGraph<N>,
    /// A cached topological ordering of the graph.
    toposort: Vec<N>,
    /// Whether the graph has been modified since the last topological sort.
    /// If `true`, the next call to [`toposort`](Dag::toposort) will
    /// recompute the topological order.
    dirty: bool,
}

impl<N: GraphNodeId> Dag<N> {
    /// Creates a new empty directed acyclic graph (DAG).
    pub fn new() -> Self {
        Self {
            graph: DiGraph::default(),
            toposort: Vec::new(),
            dirty: false,
        }
    }

    /// Adds a node to the DAG. Marks the graph as dirty, indicating that the
    /// topological sort is no longer valid.
    pub fn add_node(&mut self, node: N) {
        self.graph.add_node(node);
        self.dirty = true;
    }

    /// Removes a node from the DAG. If the node was present then the graph is
    /// marked as dirty, indicating that the topological sort is no longer valid.
    pub fn remove_node(&mut self, node: N) {
        if self.graph.remove_node(node) {
            self.dirty = true;
        }
    }

    /// Adds a directed edge from `from` to `to` in the DAG. The nodes are added
    /// to the graph if they are not already present. Marks the graph as dirty,
    /// indicating that the topological sort is no longer valid.
    pub fn add_edge(&mut self, from: N, to: N) {
        self.graph.add_edge(from, to);
        self.dirty = true;
    }

    /// Removes a directed edge from `from` to `to` in the DAG. If the edge was
    /// present then the graph is marked as dirty, indicating that the
    /// topological sort is no longer valid.
    pub fn remove_edge(&mut self, from: N, to: N) {
        if self.graph.remove_edge(from, to) {
            self.dirty = true;
        }
    }

    /// Replaces the entire graph with a new one. Marks the graph as dirty,
    /// indicating that the topological sort is no longer valid.
    pub fn set_graph(&mut self, graph: DiGraph<N>) {
        self.graph = graph;
        self.dirty = true;
    }

    pub fn try_into<M: GraphNodeId + TryFrom<N>>(self) -> Result<Dag<M>, M::Error> {
        let graph = self.graph.try_into::<M>()?;
        Ok(Dag {
            graph,
            toposort: Vec::new(),
            dirty: true,
        })
    }

    /// Sorts the DAG in topological order, and returns a [`SortedDag`]. If the
    /// graph hasn't changed (isn't dirty), the existing sorted graph is returned.
    ///
    /// # Errors
    ///
    /// If the graph contains cycles, this function will return a [`GraphToposortError`].
    pub fn toposort(&mut self) -> Result<SortedDag<'_, N>, GraphToposortError<N>> {
        if self.dirty {
            self.toposort = self.graph.toposort()?;
            self.dirty = false;
        }
        Ok(SortedDag(self))
    }
}

impl<N: GraphNodeId> Clone for Dag<N> {
    fn clone(&self) -> Self {
        Self {
            graph: self.graph.clone(),
            toposort: self.toposort.clone(),
            dirty: self.dirty,
        }
    }
}

impl<N: GraphNodeId> Default for Dag<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: GraphNodeId> Deref for Dag<N> {
    type Target = DiGraph<N>;

    fn deref(&self) -> &Self::Target {
        &self.graph
    }
}

impl<N: GraphNodeId> From<DiGraph<N>> for Dag<N> {
    fn from(graph: DiGraph<N>) -> Self {
        Self {
            graph,
            toposort: Vec::new(),
            dirty: true,
        }
    }
}

/// A topologically sorted view of a [`Dag`].
pub struct SortedDag<'a, N: GraphNodeId>(&'a mut Dag<N>);

impl<'a, N: GraphNodeId> SortedDag<'a, N> {
    pub fn reborrow(&mut self) -> SortedDag<'_, N> {
        SortedDag(self.0)
    }

    /// Converts this `SortedDag` back into the original `Dag`, useful for
    /// modifying the graph.
    pub fn into_inner(self) -> &'a mut Dag<N> {
        self.0
    }

    /// Returns an iterator over the nodes in topological order.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = N> + ExactSizeIterator {
        self.0.toposort.iter().copied()
    }

    /// Computes various properties of the DAG, such as transitive reduction,
    /// transitive closure, reachability, and connected and disconnected components.
    pub fn analyze(&self) -> DagAnalysis<N> {
        if self.0.graph.node_count() == 0 {
            return DagAnalysis::default();
        }

        let n = self.0.graph.node_count();

        // build a copy of the graph where the nodes and edges appear in topsorted order
        let mut map = <HashMap<_, _>>::with_capacity_and_hasher(n, Default::default());
        let mut topsorted = DiGraph::<N>::default();
        // iterate nodes in topological order
        for (i, node) in self.iter().enumerate() {
            map.insert(node, i);
            topsorted.add_node(node);
            // insert nodes as successors to their predecessors
            for pred in self.neighbors_directed(node, Incoming) {
                topsorted.add_edge(pred, node);
            }
        }

        let mut reachable = FixedBitSet::with_capacity(n * n);
        let mut connected = <HashSet<_>>::default();
        let mut disconnected = Vec::new();

        let mut transitive_edges = Vec::new();
        let mut transitive_reduction = DiGraph::default();
        let mut transitive_closure = DiGraph::default();

        let mut visited = FixedBitSet::with_capacity(n);

        // iterate nodes in topological order
        for node in topsorted.nodes() {
            transitive_reduction.add_node(node);
            transitive_closure.add_node(node);
        }

        // iterate nodes in reverse topological order
        for a in topsorted.nodes().rev() {
            let index_a = *map.get(&a).unwrap();
            // iterate their successors in topological order
            for b in topsorted.neighbors_directed(a, Outgoing) {
                let index_b = *map.get(&b).unwrap();
                debug_assert!(index_a < index_b);
                if !visited[index_b] {
                    // edge <a, b> is not redundant
                    transitive_reduction.add_edge(a, b);
                    transitive_closure.add_edge(a, b);
                    reachable.insert(index(index_a, index_b, n));

                    let successors = transitive_closure
                        .neighbors_directed(b, Outgoing)
                        .collect::<Vec<_>>();
                    for c in successors {
                        let index_c = *map.get(&c).unwrap();
                        debug_assert!(index_b < index_c);
                        if !visited[index_c] {
                            visited.insert(index_c);
                            transitive_closure.add_edge(a, c);
                            reachable.insert(index(index_a, index_c, n));
                        }
                    }
                } else {
                    // edge <a, b> is redundant
                    transitive_edges.push((a, b));
                }
            }

            visited.clear();
        }

        // partition pairs of nodes into "connected by path" and "not connected by path"
        for i in 0..(n - 1) {
            // reachable is upper triangular because the nodes were topsorted
            for index in index(i, i + 1, n)..=index(i, n - 1, n) {
                let (a, b) = row_col(index, n);
                let pair = (self.0.toposort[a], self.0.toposort[b]);
                if reachable[index] {
                    connected.insert(pair);
                } else {
                    disconnected.push(pair);
                }
            }
        }

        // fill diagonal (nodes reach themselves)
        // for i in 0..n {
        //     reachable.set(index(i, i, n), true);
        // }

        DagAnalysis {
            reachable,
            connected,
            disconnected,
            transitive_edges,
            transitive_reduction,
            transitive_closure,
        }
    }

    /// Removes redundant edges from the graph via transitive reduction.
    ///
    /// The provided `analysis` must be the result of a previous call to
    /// [`analyze`](SortedDag::analyze) on the same graph, without any changes
    /// to the graph structure.
    pub fn remove_redundant_edges(&mut self, analysis: &DagAnalysis<N>) {
        // We don't need to mark the graph as dirty here, because transitive
        // reduction does not change the topological order of the graph.
        self.0.graph = analysis.transitive_reduction.clone();
    }
}

impl<N: GraphNodeId> Deref for SortedDag<'_, N> {
    type Target = Dag<N>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

/// Stores the results of [`SortedDag::analyze`].
pub struct DagAnalysis<N: GraphNodeId> {
    /// Boolean reachability matrix for the graph.
    pub(crate) reachable: FixedBitSet,
    /// Pairs of nodes that have a path connecting them.
    pub(crate) connected: HashSet<(N, N)>,
    /// Pairs of nodes that don't have a path connecting them.
    pub(crate) disconnected: Vec<(N, N)>,
    /// Edges that are redundant because a longer path exists.
    pub(crate) transitive_edges: Vec<(N, N)>,
    /// Variant of the graph with no transitive edges.
    pub(crate) transitive_reduction: DiGraph<N>,
    /// Variant of the graph with all possible transitive edges.
    // TODO: this will very likely be used by "if-needed" ordering
    #[expect(dead_code, reason = "See the TODO above this attribute.")]
    pub(crate) transitive_closure: DiGraph<N>,
}

impl<N: GraphNodeId> Default for DagAnalysis<N> {
    fn default() -> Self {
        Self {
            reachable: FixedBitSet::new(),
            connected: HashSet::default(),
            disconnected: Vec::new(),
            transitive_edges: Vec::new(),
            transitive_reduction: DiGraph::default(),
            transitive_closure: DiGraph::default(),
        }
    }
}

/// Converts 2D row-major pair of indices into a 1D array index.
pub(crate) fn index(row: usize, col: usize, num_cols: usize) -> usize {
    debug_assert!(col < num_cols);
    (row * num_cols) + col
}

/// Converts a 1D array index into a 2D row-major pair of indices.
pub(crate) fn row_col(index: usize, num_cols: usize) -> (usize, usize) {
    (index / num_cols, index % num_cols)
}
