use alloc::{vec, vec::Vec};
use variadics_please::all_tuples;

use crate::schedule2::GraphNode;

/// Stores configuration for a single node in a graph.
///
/// The configuration includes the node itself, and metadata used to configure
/// the graph.
pub struct NodeConfig<N: GraphNode> {
    pub(crate) node: N,
    pub(crate) metadata: N::Metadata,
}

/// Stores configuration for a group of nodes in a graph.
pub enum NodeConfigs<N: GraphNode> {
    /// Configuration for a single node.
    Single(NodeConfig<N>),
    /// Configuration for a group of nested configurations
    Group {
        /// Configuration for each element in the group.
        configs: Vec<NodeConfigs<N>>,
        /// Metadata for the whole group.
        metadata: N::GroupMetadata,
    },
}

/// Types that can be converted into a [`NodeConfigs`].
///
/// # Usage notes
///
/// This trait should only be used as a bound for trait implementations or as an
/// argument to a function. If node configs need to be returned from a
/// function or stored somewhere, use [`NodeConfigs`] instead of this trait.
///
/// # Examples
///
/// ```
/// # use bevy_ecs::schedule::IntoSystemConfigs;
/// # struct AppMock;
/// # struct Update;
/// # impl AppMock {
/// #     pub fn add_systems<M>(
/// #         &mut self,
/// #         schedule: Update,
/// #         systems: impl IntoSystemConfigs<M>,
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
pub trait IntoNodeConfigs<N: GraphNode, Marker>: Sized {
    /// Converts this value into a [`NodeConfigs`].
    fn into_configs(self) -> NodeConfigs<N>;
}

/// Singular [`NodeConfig`]s can be converted into [`NodeConfigs`].
impl<N: GraphNode> IntoNodeConfigs<N, ()> for NodeConfig<N> {
    fn into_configs(self) -> NodeConfigs<N> {
        NodeConfigs::Single(self)
    }
}

/// [`NodeConfigs`] can be converted into themselves.
impl<N: GraphNode> IntoNodeConfigs<N, ()> for NodeConfigs<N> {
    fn into_configs(self) -> NodeConfigs<N> {
        self
    }
}

#[doc(hidden)]
pub struct NodeConfigTupleMarker;

macro_rules! impl_system_collection {
    ($(#[$meta:meta])* $(($param: ident, $sys: ident)),*) => {
        $(#[$meta])*
        impl<$($param, $sys),*, N: GraphNode> IntoNodeConfigs<N, (NodeConfigTupleMarker, $($param,)*)> for ($($sys,)*)
        where
            $($sys: IntoNodeConfigs<N, $param>),*
        {
            #[expect(
                clippy::allow_attributes,
                reason = "We are inside a macro, and as such, `non_snake_case` is not guaranteed to apply."
            )]
            #[allow(
                non_snake_case,
                reason = "Variable names are provided by the macro caller, not by us."
            )]
            fn into_configs(self) -> NodeConfigs<N> {
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
    impl_system_collection,
    1,
    20,
    P,
    S
);
