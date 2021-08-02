{-
  An encoding of the well-typed nonterminating term of System U
  from "A simplification of Girard's paradox": https://doi.org/10.1007/BFb0014058
-}

-- The uninhabited type
Empty : Type
Empty = (p : Type) -> p

-- Negation: ¬x = x → ∀p. p = x → ⊥
neg : Type -> Type
neg x = x -> Empty

-- Powerset: ℘S = S → Type
P : Type -> Type
P s = s -> Type

-- A powerful paradoxical universe:
-- For every C ∈ ℘℘U, στC = {X : {y : τσy ∈ X} ∈ C}.
U : Type
U = (x: Type) -> ((P (P x)) -> x) -> P (P x)

-- A mapping from ℘℘U to U
tau : (t: P (P U)) -> U
tau t x f p = t (\s: U => p (f (s x f)))

-- A mapping from U to ℘℘U
sigma : U -> P (P U)
sigma s = (s U) (\t: P (P U) => tau t)

-- A normal term of type ℘U
Delta : P U
Delta y = neg ((p: P U) -> sigma y p -> p (tau (sigma y)))

-- A term of type U
Omega : U
Omega = tau (\p: P U => (x: U) -> sigma x p -> p x)

-- From Section 7: Along with terms P and Q, we have the reduction
-- L R --> (Q M) R --> (P M) R --> L R --> ...

R : (p: P U) -> ((x: U) -> sigma x p -> p x) -> p Omega
R _ one = one Omega (\x => one (tau (sigma x)))

M : (x: U) -> sigma x Delta -> Delta x
M _ two three = three Delta two (\p => three (\y => p (tau (sigma y))))

L : neg ((p: P U) -> ((x: U) -> sigma x p -> p x) -> p Omega)
L zero = zero Delta M (\p => zero (\y => p (tau (sigma y))))

-- A term of type ⊥ = ∀p. p
empty : Empty
empty = L R

-- This version with no let bindings loops in Idris
empty' : Empty
empty' = ? {-
  (\zero: ((p: P U) -> ((x: U) -> sigma x p -> p x) -> p Omega) =>
    (zero Delta (\x, two, three => three Delta two (\p => three (\y => p (tau (sigma y))))))
    (\p => zero (\y => p (tau (sigma y)))))
  (\p, one => one Omega (\x => one (tau (sigma x)))) -}
