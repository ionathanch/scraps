-- https://chitter.xyz/@niss/112479262797739945
-- https://github.com/agda/agda/issues/1556

open import Relation.Binary.PropositionalEquality

data Ctx : Set
Type : Ctx → Set

data Ctx where
  ∙ : Ctx
  _∷_ : ∀ Γ → Type Γ → Ctx

★′ : ∀ {Γ} → Type Γ
rename′ : ∀ {Γ Δ} → Type Γ → Type Δ
rename★′ : ∀ {Γ Δ} → rename′ {Γ} {Δ} ★′ ≡ ★′

data Term Γ : Type Γ → Set
data In : ∀ Γ → Type Γ → Set
rename : ∀ {Γ Δ A} → (In Γ A → In Δ (rename′ A)) → Term Γ A → Term Δ (rename′ A)

data In where
  here : ∀ Γ A → In (Γ ∷ A) (rename′ A)
  there : ∀ Γ A B → In Γ A → In (Γ ∷ B) (rename′ A)

Type Γ = Term Γ ★′

data Term Γ where
  var : ∀ A → In Γ A → Term Γ A
  ★ : Type Γ

★′ = ★

rename ρ ★ = subst (Term _) (sym rename★′) ★′
rename ρ (var A where?) = var (rename′ A) (ρ where?)

-- This loops the type checker!!
-- rename′ ★ = ★

rename′ x = subst (Term _) rename★′ (rename (λ where? → subst (In _) (sym rename★′) {!   !}) x)

rename★′ = {! refl !}