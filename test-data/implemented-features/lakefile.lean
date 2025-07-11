import Lake
open Lake DSL

package «implemented-features» where
  -- Lean compiler version
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «ImplementedFeatures» where
  -- Library configuration
  roots := #[`Syntax, `Semantics]