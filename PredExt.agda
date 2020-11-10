open import Data.Bool
open import Data.Product
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality

postulate predExt : (P Q : Bool → Set) → ((b : Bool) → (P b → Q b) × (Q b → P b)) → P ≡ Q

propExt : (P Q : Set) → (P → Q) × (Q → P) → P ≡ Q
propExt P Q PQ = cong (λ f → f true) (predExt (λ _ → P) (λ _ → Q) (λ _ → PQ))
