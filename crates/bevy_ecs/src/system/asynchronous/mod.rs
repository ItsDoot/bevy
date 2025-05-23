mod function_system;
pub mod point;
mod system;
mod system_param;

pub use function_system::*;
pub use system::*;
pub use system_param::*;

#[cfg(test)]
mod tests {
    use crate::{prelude::Resource, system::Res};

    use super::{Async, AsyncCtx};

    #[derive(Resource)]
    struct Bar;

    async fn my_system(mut world: AsyncCtx, mut bar: Async<'_, Res<'_, Bar>>) {
        let bar = bar.asap(&mut world).await;
        todo!()
    }
}
