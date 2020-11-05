{-
  An encoding of the well-typed nonterminating term of System U
  from "A simplification of Girard's paradox": https://doi.org/10.1007/BFb0014058
-}

-- negation ¬x = x → ∀p. p = x → ⊥
neg : Type -> Type
neg x = x -> (p: Type) -> p

-- powerset ℘S = S → Type
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

-- A (normal) term of type U
Omega : U
-- Omega = tau (\p: P U => (x: U) -> sigma x p -> p x)
{- Omega x f p = (s: U) -> ((sigma s) (\y: U => (p (f ((y x) f))))) -> (p (f ((s x) f))) -}

-- A term of type ⊥ = ∀p. p
void : (p: Type) -> p
void =
  (\zero: ((p: P U) -> ((x: U) -> sigma x p -> p x) -> p Omega) =>
    (zero Delta
      (\x: U, two: sigma x Delta, three: ((p: P U) -> sigma x p -> p (tau (sigma x))) =>
        three Delta two
          (\p: P U =>
            three
              (\y: U =>
                p (tau (sigma y))))))
    (\p: P U =>
      zero
        (\y: U =>
          p (tau (sigma y)))))
  (\p: P U, one: ((x: U) -> sigma x p -> p x) =>
    one Omega
      (\x: U =>
        one (tau (sigma x))))
