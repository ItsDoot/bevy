use bevy_ecs::schedule::Chain;

#[derive(Default)]
pub struct RenderNodeMetadata {}

#[derive(Default)]
pub struct RenderGroupMetadata {
    pub chained: Chain,
}

impl AsMut<Chain> for RenderGroupMetadata {
    fn as_mut(&mut self) -> &mut Chain {
        &mut self.chained
    }
}
