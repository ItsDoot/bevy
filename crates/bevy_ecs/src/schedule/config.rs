use alloc::{vec, vec::Vec};
use variadics_please::all_tuples;

use crate::schedule::traits::{GraphNode, ScheduleGraph};

/// Stores configuration for a single generic node (a system or a system set)
///
/// The configuration includes the node itself, scheduling metadata
/// (hierarchy: in which sets is the node contained,
/// dependencies: before/after which other nodes should this node run)
/// and the run conditions associated with this node.
pub struct NodeConfig<N: GraphNode<G>, G: ScheduleGraph> {
    pub(crate) node: N,
    pub(crate) metadata: N::Metadata,
}

/// A collections of generic [`NodeConfig`]s.
pub enum NodeConfigs<N: GraphNode<G>, G: ScheduleGraph> {
    /// Configuration for a single node.
    Single(NodeConfig<N, G>),
    /// Configuration for a nested group of nodes.
    Group {
        /// Configuration for each element of the group.
        configs: Vec<NodeConfigs<N, G>>,
        /// Metadata applied to all elements in the group.
        metadata: N::GroupMetadata,
    },
}

/// Types that can convert into a [`NodeConfigs`].
///
/// This trait is implemented for "systems" (functions whose arguments all implement
/// [`SystemParam`](crate::system::SystemParam)), or tuples thereof.
/// It is a common entry point for system configurations.
///
/// # Usage notes
///
/// This trait should only be used as a bound for trait implementations or as an
/// argument to a function. If system configs need to be returned from a
/// function or stored somewhere, use [`NodeConfigs`] instead of this trait.
///
/// # Examples
///
/// ```
/// # use bevy_ecs::schedule::IntoNodeConfigs;
/// # struct AppMock;
/// # struct Update;
/// # impl AppMock {
/// #     pub fn add_systems<M>(
/// #         &mut self,
/// #         schedule: Update,
/// #         systems: impl IntoNodeConfigs<ScheduledSystem, M>,
/// #    ) -> &mut Self { self }
/// # }
/// # let mut app = AppMock;
///
/// fn handle_input() {}
///
/// fn update_camera() {}
/// fn update_character() {}
///
/// app.add_systems(
///     Update,
///     (
///         handle_input,
///         (update_camera, update_character).after(handle_input)
///     )
/// );
/// ```
#[diagnostic::on_unimplemented(
    message = "`{Self}` does not describe a valid system configuration",
    label = "invalid system configuration"
)]
pub trait IntoNodeConfigs<N: GraphNode<G>, G: ScheduleGraph, Marker>: Sized {
    /// Converts this value into a [`NodeConfigs`].
    fn into_configs(self) -> NodeConfigs<N, G>;
}

/// Singular [`NodeConfig`]s can be converted into [`NodeConfigs`].
impl<N: GraphNode<G>, G: ScheduleGraph> IntoNodeConfigs<N, G, ()> for NodeConfig<N, G> {
    fn into_configs(self) -> NodeConfigs<N, G> {
        NodeConfigs::Single(self)
    }
}

/// [`NodeConfigs`] can be converted into themselves.
impl<N: GraphNode<G>, G: ScheduleGraph> IntoNodeConfigs<N, G, ()> for NodeConfigs<N, G> {
    fn into_configs(self) -> NodeConfigs<N, G> {
        self
    }
}

#[doc(hidden)]
pub struct NodeConfigTupleMarker;

macro_rules! impl_node_type_collection {
    ($(#[$meta:meta])* $(($param: ident, $sys: ident)),*) => {
        $(#[$meta])*
        impl<$($param, $sys),*, N: GraphNode<G>, G: ScheduleGraph> IntoNodeConfigs<N, G, (NodeConfigTupleMarker, $($param,)*)> for ($($sys,)*)
        where
            $($sys: IntoNodeConfigs<N, G, $param>),*
        {
            #[expect(
                clippy::allow_attributes,
                reason = "We are inside a macro, and as such, `non_snake_case` is not guaranteed to apply."
            )]
            #[allow(
                non_snake_case,
                reason = "Variable names are provided by the macro caller, not by us."
            )]
            fn into_configs(self) -> NodeConfigs<N, G> {
                let ($($sys,)*) = self;
                NodeConfigs::Group {
                    configs: vec![$($sys.into_configs(),)*],
                    metadata: Default::default(),
                }
            }
        }
    }
}

all_tuples!(
    #[doc(fake_variadic)]
    impl_node_type_collection,
    1,
    20,
    P,
    S
);
