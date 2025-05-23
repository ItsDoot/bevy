use core::marker::PhantomData;
use std::future::Future;

use variadics_please::all_tuples;

use crate::system::SystemInput;

use super::{AsyncSystemParam, AsyncSystemParamItem};

pub struct AsyncFunctionSystem<Marker, F>
where
    F: AsyncSystemParamFunction<Marker>,
{
    func: F,
    marker: PhantomData<fn() -> Marker>,
}

/// A trait implemented for all async functions that can be used as [`AsyncSystem`]s.
///
/// This trait can be useful for making your own async systems which accept other async systems,
/// sometimes called higher order async systems.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a valid async system",
    label = "invalid async system"
)]
pub trait AsyncSystemParamFunction<Marker>: Send + Sync + 'static {
    /// The input type of this async system. See [`AsyncSystem::In`].
    type In: SystemInput;
    /// The return type of this async system. See [`AsyncSystem::Out`].
    type Out;
    /// The [`AsyncSystemParam`]s used by this system to access the [`World`].
    type Param: AsyncSystemParam;

    /// Executes this async system once. See [`AsyncSystem::run`].
    fn run<'s>(
        &'s mut self,
        input: <Self::In as SystemInput>::Inner<'s>,
        param: AsyncSystemParamItem<Self::Param>,
    ) -> impl Future<Output = Self::Out> + Send + 's;
}

/// A marker type used to distinguish async function systems with and without input.
#[doc(hidden)]
pub struct HasAsyncSystemInput;

macro_rules! impl_async_system_function {
    ($($param: ident),*) => {
        #[expect(
            clippy::allow_attributes,
            reason = "This is within a macro, and as such, the below lints may not always apply."
        )]
        #[allow(
            non_snake_case,
            reason = "Certain variable names are provided by the caller, not by us."
        )]
        impl<Out, Func, $($param: AsyncSystemParam),*> AsyncSystemParamFunction<fn($($param,)*) -> Out> for Func
        where
            Out: 'static,
            Func: Send + Sync + 'static,
            for<'a> &'a mut Func:
                AsyncFnMut($($param),*) -> Out +
                AsyncFnMut($(AsyncSystemParamItem<$param>),*) -> Out
        {
            type In = ();
            type Out = Out;
            type Param = ($($param,)*);
            #[inline]
            fn run<'s>(&'s mut self, _input: (), param: AsyncSystemParamItem<($($param,)*)>) -> impl Future<Output = Out> + Send + 's {
                async fn call_inner<Out, $($param,)*>(mut f: impl AsyncFnMut($($param,)*) -> Out, $($param: $param,)*) -> Out {
                    f($($param,)*).await
                }
                let ($($param,)*) = param;
                call_inner(self, $($param),*)
            }
        }
    };
}

all_tuples!(impl_async_system_function, 0, 1, F);
