import Lake

open Lake DSL

package «scraps» where

@[default_target]
lean_lib «scraps» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
