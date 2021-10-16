open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Equality

data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) → (B x → W A B) → W A B

syntax W A (λ x → B) = W[ x ∈ A ] B

data U : Set
El : U → Set

data U where
  bot   : U
  top   : U
  pi    : (a : U) → (El a → U) → U
  sigma : (a : U) → (El a → U) → U
  sum   : (a b : U) → U
  eq    : ∀ {a : U} → (x y : El a) → U
  w     : (a : U) → (El a → U) → U

El bot = ⊥
El top = ⊤
El (pi a b) = (x : El a) → El (b x)
El (sigma a b) = Σ[ x ∈ El a ] El (b x)
El (sum a b) = El a ⊎ El b
El (eq x y) = x ≡ y
El (w a b) = W[ x ∈ El a ] El (b x)
