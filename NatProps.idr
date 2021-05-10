{-
  Some generic properties of naturals
-}

%default total

-- Zero is not equal to any successor

-- The induction principle for equality
J : forall A. (P : (x, y : A) -> (p : x = y) -> Type) -> (d : (x : A) -> P x x Refl) ->
  (x, y : A) -> (p : x = y) -> P x y p
J _ d x x Refl = d x

subst: forall A. (P : A -> Type) -> (x, y : A) -> x === y -> P x -> P y
subst f = J (\x, y, _ => f x -> f y) (\_, fx => fx)
-- subst f _ _ Refl px = px

cong: forall A, B. (f: A -> B) -> (x, y: A) -> x === y -> f x === f y
cong f x y p = subst (\y => f x === f y) x y p Refl
-- cong f _ _ Refl = Refl

data Bottom: Type where

discnat: Nat -> Type
discnat Z = Bottom
discnat (S n) = Nat

zeroOnen't: (n: Nat) -> S n === Z -> Bottom
zeroOnen't n p = subst (\t => t) Nat Bottom (cong discnat (S n) Z p) Z

-- Successor is injective, via:
-- * Pattern-matching,
-- * The J eliminator, and
-- * Case expressions

injRefl: {n, m : Nat} -> S n === S m -> n === m
injRefl Refl = Refl

injJ: {n, m : Nat} -> S n === S m -> n === m
injJ p = J P d (S n) (S m) p
  where
    P: (n, m : Nat) -> (p: n === m) -> Type
    P (S n) (S m) _ = n === m
    P Z Z _ = Unit
    d: (n : Nat) -> P n n Refl
    d (S n) = Refl
    d Z = ()

injCase: {n, m : Nat} -> S n === S m -> n === m
injCase p =
  case p of
    Refl {x = S n} => Refl {x = n}
