open import Generics.Prelude hiding (_≟_)
open import Generics.Telescope
open import Generics.Desc
open import Generics.All
open import Generics.HasDesc
open import Generics.Constructions.DecEq renaming (_≟_ to _⩵_)

open import Agda.Primitive
open import Data.Fin using (_≟_ ; _<_)
open import Relation.Nullary using (yes ; no)

{-# NO_UNIVERSE_CHECK #-}
record Ord {ℓ} (A : Set ℓ) : Setω where
  field
    _<ᵒ_ : A → A → Setω
open Ord ⦃...⦄ public

module _ {P I ℓ} {A : Indexed P I ℓ} (H : HasDesc {P} {I} A) where
  open HasDesc H
  open import Generics.Helpers P I DecEq (λ _ → ⊤) (λ _ → ⊤ω) as Helpers

  OrdHelpers : ∀ p → Setω
  OrdHelpers p = Helpers p D

  private module _ {p} (OH : OrdHelpers p) where
    variable
      V : ExTele P
      v : ⟦ V ⟧tel p
      i : ⟦ I ⟧tel p

    mutual
      ordIndArg : (C : ConDesc P V I) (x y : ⟦ C ⟧IndArg A′ (p , v)) →
        AllIndArgω Acc C x → AllIndArgω Acc C y → Setω
      ordIndArg (var _) x y accx accy = ord-wf x y accx accy
      ordIndArg (π ai S C) x y accx accy = ∀ s → ordIndArg C (app< ai > x s) (app< ai > y s) (accx s) (accy s)
      ordIndArg (A ⊗ B) (xa , xb) (ya , yb) (accxa , accxb) (accya , accyb) =
        ordIndArg A xa ya accxa accya ×ω ordIndArg B xb yb accxb accyb

      ordCon : (C : ConDesc P V I) (H : ConHelper p C) (x y : ⟦ C ⟧Con A′ (p , v , i)) →
        AllConω Acc C x → AllConω Acc C y → Setω
      ordCon _ var refl refl _ _ = ⊤ω
      ordCon _ (pi-irr ⦃ _ ⦄ ⦃ H ⦄) (irrv _ , x) (irrv _ , y) accx accy = ordCon _ H x y accx accy
      ordCon _ (pi-rel ⦃ ord ⦄ ⦃ H ⦄) (sx , x) (sy , y) accx accy with sx ⩵ sy
      ... | yes refl = ordCon _ H x y accx accy
      ... | no _ = ⊥ω
      ordCon .(A ⊗ B) (prod {A} {B} ⦃ Ha ⦄ ⦃ Hb ⦄) (xa , xb) (ya , yb) (accxa , accxb) (accya , accyb) =
        ordIndArg A xa ya accxa accya ×ω ordCon B Hb xb yb accxb accyb

      ord-wf : ∀ (x y : A′ (p , i)) → Acc x → Acc y → Setω
      ord-wf x y (acc ax) (acc ay) with split x | split y
      ord-wf x y (acc ax) (acc ay) | (kx , x') | (ky , y') with kx ≟ ky
      ord-wf x y (acc ax) (acc ay) | (kx , x') | (ky , y') | no _ = Liftω (kx < ky)
      ord-wf x y (acc ax) (acc ay) | (k  , x') | (k  , y') | yes refl =
        ordCon (lookupCon D k) (lookupHelper OH k) x' y' ax ay
    
  deriveOrd : ∀ {p} ⦃ OH : OrdHelpers p ⦄ {i} → Ord (A′ (p , i))
  deriveOrd ⦃ OH ⦄ ._<ᵒ_ x y = ord-wf OH x y (wf x) (wf y)