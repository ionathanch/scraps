{-
  A reproduction of the proof that impredicativity with propositional extensionality yields non-normalization
  from "Failure of Normalization in Impredicative Type Theory with Proof-Irrelevant Propositional Equality":
  https://doi.org/10.23638/LMCS-16(2:14)2020
-}

Prop : Type
Prop = Type

propext : {0 A, B : Prop} -> (A -> B) -> (B -> A) -> A === B
tautext : {0 A, B : Prop} -> A -> B -> A === B
tautext a b = propext (\_ => b) (\_ => a)

J : forall A. (P : (x, y : A) -> (p : x === y) -> Type) -> (d : (x : A) -> P x x Refl) ->
  (x, y : A) -> (p : x === y) -> P x y p
J _ d x x Refl = d x

cast : {A, B : Prop} -> A === B -> A -> B
cast = J (\a, b, _ => a -> b) (\_ => id) A B

-- The impredicative identity type
T : Prop
T = (A : Prop) -> A -> A

-- Suppose T = (A : Type{0}) -> A -> A
-- Then T -> T : Type{1}, which doesn't fit into z,
-- not unless we use impredicative Prop instead
delta : T -> T
delta z = z (T -> T) (id {a = T}) z

-- If you have a proof of an arbitrary type A,
-- then that type is equal to (T -> T) by extensionality,
-- and you can cast to any A from delta
omega : T
omega _ a = cast (tautext (id {a = T}) a) delta

Omega : T
Omega = delta omega -- = omega (T -> T) id (delta omega)
