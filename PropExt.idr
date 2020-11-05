{-
  A reproduction of the proof that impredicativity with propositional extensionality yields non-normalization
  from "Failure of Normalization in Impredicative Type Theory with Proof-Irrelevant Propositional Equality":
  https://doi.org/10.23638/LMCS-16(2:14)2020
-}

tautext : forall A, B. A -> B -> A === B

J : forall A. (P : (x, y : A) -> (p : x === y) -> Type) -> (d : (x : A) -> P x x Refl) ->
  (x, y : A) -> (p : x === y) -> P x y p
J _ d x x Refl = d x

cast : {A, B : Type} -> A === B -> A -> B
cast = J (\a, b, _ => a -> b) (\_ => id) A B

T : Type
T = (A : Type) -> A -> A

delta : T -> T
delta z = z (T -> T) id z

omega : T
omega _ a = cast (tautext id a) delta

Omega : T
Omega = delta omega
