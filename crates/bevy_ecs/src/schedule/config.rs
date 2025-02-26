use alloc::{boxed::Box, vec, vec::Vec};

use variadics_please::all_tuples;

use crate::{
    result::Result,
    schedule::{
        traits::{GraphNode, ScheduleGraph},
        InternedSystemSet, SystemSet,
    },
    system::{BoxedSystem, InfallibleSystemWrapper, IntoSystem, SystemInput},
};

/// Stores configuration for a single generic node (a system or a system set)
///
/// The configuration includes the node itself, scheduling metadata
/// (hierarchy: in which sets is the node contained,
/// dependencies: before/after which other nodes should this node run)
/// and the run conditions associated with this node.
pub struct NodeConfig<N: GraphNode<G>, G: ScheduleGraph> {
    /// The node itself.
    pub node: N,
    /// Additional data used to configure the node.
    pub metadata: N::Metadata,
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

/// [`System`]s that cannot fail can be converted into [`NodeConfigs`] for a
/// given supported [`ScheduleGraph`].
///
/// [`System`]: crate::system::System
pub struct InfallibleSystem<In: SystemInput = (), Out = ()>(pub BoxedSystem<In, Out>);

impl<In, Out, G, F, Marker> IntoNodeConfigs<InfallibleSystem<In, Out>, G, (Infallible, Marker)>
    for F
where
    In: SystemInput + 'static,
    Out: 'static,
    InfallibleSystem<In, Out>: GraphNode<G>,
    G: ScheduleGraph,
    F: IntoSystem<In, Out, Marker>,
{
    fn into_configs(self) -> NodeConfigs<InfallibleSystem<In, Out>, G> {
        let system = Box::new(IntoSystem::into_system(self));
        NodeConfigs::Single(InfallibleSystem(system).into_config())
    }
}

impl<In, Out, G> IntoNodeConfigs<InfallibleSystem<In, Out>, G, ()> for BoxedSystem<In, Out>
where
    In: SystemInput + 'static,
    Out: 'static,
    InfallibleSystem<In, Out>: GraphNode<G>,
    G: ScheduleGraph,
{
    fn into_configs(self) -> NodeConfigs<InfallibleSystem<In, Out>, G> {
        NodeConfigs::Single(InfallibleSystem(self).into_config())
    }
}

/// [`System`]s that can return a result can be converted into [`NodeConfigs`]
/// for a given supported [`ScheduleGraph`].
///
/// [`InfallibleSystemWrapper`] is used to support systems that do not return a
/// result.
///
/// [`System`]: crate::system::System
pub struct FallibleSystem<In: SystemInput = (), Out = ()>(pub BoxedSystem<In, Result<Out>>);

/// Marker component to allow for conflicting implementations of [`IntoNodeConfigs`]
#[doc(hidden)]
pub struct Infallible;

impl<In, Out, G, F, Marker> IntoNodeConfigs<FallibleSystem<In, Out>, G, (Infallible, Marker)> for F
where
    In: SystemInput + 'static,
    Out: 'static,
    FallibleSystem<In, Out>: GraphNode<G>,
    G: ScheduleGraph,
    F: IntoSystem<In, Out, Marker>,
{
    fn into_configs(self) -> NodeConfigs<FallibleSystem<In, Out>, G> {
        let system = Box::new(InfallibleSystemWrapper::new(IntoSystem::into_system(self)));
        NodeConfigs::Single(FallibleSystem(system).into_config())
    }
}

/// Marker component to allow for conflicting implementations of [`IntoNodeConfigs`]
#[doc(hidden)]
pub struct Fallible;

impl<In, Out, G, F, Marker> IntoNodeConfigs<FallibleSystem<In, Out>, G, (Fallible, Marker)> for F
where
    In: SystemInput + 'static,
    Out: 'static,
    FallibleSystem<In, Out>: GraphNode<G>,
    G: ScheduleGraph,
    F: IntoSystem<In, Result<Out>, Marker>,
{
    fn into_configs(self) -> NodeConfigs<FallibleSystem<In, Out>, G> {
        let system = Box::new(IntoSystem::into_system(self));
        NodeConfigs::Single(FallibleSystem(system).into_config())
    }
}

impl<In, Out, G> IntoNodeConfigs<FallibleSystem<In, Out>, G, ()> for BoxedSystem<In, Result<Out>>
where
    In: SystemInput + 'static,
    Out: 'static,
    FallibleSystem<In, Out>: GraphNode<G>,
    G: ScheduleGraph,
{
    fn into_configs(self) -> NodeConfigs<FallibleSystem<In, Out>, G> {
        NodeConfigs::Single(FallibleSystem(self).into_config())
    }
}

impl<S: SystemSet, G: ScheduleGraph> IntoNodeConfigs<InternedSystemSet, G, ()> for S
where
    InternedSystemSet: GraphNode<G>,
{
    fn into_configs(self) -> NodeConfigs<InternedSystemSet, G> {
        NodeConfigs::Single(self.intern().into_config())
    }
}
