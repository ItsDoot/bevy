use bevy_ecs::schedule::{Chain, Dependencies, Hierarchy, InternedSystemSet};

#[derive(Default)]
pub struct RenderNodeMetadata {
    pub hierarchy: Hierarchy<InternedSystemSet>,
    pub dependencies: Dependencies<InternedSystemSet>,
}

impl AsMut<Hierarchy<InternedSystemSet>> for RenderNodeMetadata {
    fn as_mut(&mut self) -> &mut Hierarchy<InternedSystemSet> {
        &mut self.hierarchy
    }
}

impl AsMut<Dependencies<InternedSystemSet>> for RenderNodeMetadata {
    fn as_mut(&mut self) -> &mut Dependencies<InternedSystemSet> {
        &mut self.dependencies
    }
}

#[derive(Default)]
pub struct RenderGroupMetadata {
    pub chained: Chain,
}

impl AsMut<Chain> for RenderGroupMetadata {
    fn as_mut(&mut self) -> &mut Chain {
        &mut self.chained
    }
}
