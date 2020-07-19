{-
  Some properties about equalities.
-}

-- Properties of Martin-Löf equality.
-- `sym`, `trans`, and `cong` are already defined in Prelude.
sym' : x = y -> y = x
sym' Refl = Refl

trans' : x = y -> y = z -> x = z
trans' Refl Refl = Refl

-- Generalized congruence over the functions
congG : x = y -> f = g -> f x = g y
congG Refl Refl = Refl

-- Indiscernibility of identicals, i.e. congruence
-- It could probably also be written using congG,
-- but this proof is far shorter and cleaner.
cong' : x = y -> (forall f. f x = f y)
cong' Refl = Refl

-- This is also the indiscernibility of identicals,
-- where the property applied is P(f) = f x.
congApp : f = g -> f x = g x
congApp = congG Refl

{-
  The converse of congruence is the identity of indiscernibles:
    idind: (forall f. f x = f y) -> x = y
  A related notion is functional extensionality (the converse of congApp):
    ext: (forall x. f x = g x) -> f = g
  I don't think these can be proven.
-}

subst : forall f. x = y -> f x -> f y
subst Refl fx = fx

-- Like congApp, we can also prove this as
--    substapp = subst {f = \f => f x}
substApp : f = g -> f x -> g x
substApp Refl fx = fx


-- Properties of Leibniz equality.
infix 9 .=.
(.=.) : a -> a -> Type
(.=.) x y = forall P. P x -> P y

{-
  Leibniz equality could also be defined as a datatype:
    data (.=.) : a -> a -> Type where
      LRefl : P x -> P y -> x .=. y
  That is, a proof of x .=. y takes as argument a term
  of type P x -> P y, which is a function from P x to P y.
  Compare with the datatype for M-L equality:
    data (=) : a -> a -> Type where
      Refl : x = x
-}

lRefl : x .=. x
lRefl = \px => px

lTrans : x .=. y -> y .=. z -> x .=. z
lTrans xeqy yeqz = \px: P x => yeqz {P} (xeqy {P} px)

-- For some Q, xeqy is a function from Q x to Q y.
-- Instantiating Q as \z => P z -> P x,
-- xeqy Q is a function (P x -> P x) -> (P y -> P x).
-- Then xeqy Q lRefl is the proof of P y -> P x we need.
lSym : x .=. y -> y .=. x
lSym xeqy = xeqy {P = \z => P z -> P x} (lRefl {P})


-- We prove that Martin-Löf equality and Leibniz equality are... equal?

MLtoL : x = y -> x .=. y
MLtoL Refl px = px

-- For some Q, xeqy is a function from Q x to Q y.
-- Instantiating Q as \z => x = z,
-- xeqy Q is a function x = x -> x = y.
-- Then xeqy Q Refl is the proof of x = y we need.
LtoML : x .=. y -> x = y
LtoML xeqy = xeqy {P = \z => x = z} Refl

{-
  Notice that if we expand the type of LtoML, we have
    LtoML : (forall P. P x -> P y) -> x = y
  Then if (forall Q. Q x = Q y) -> (forall P. P x -> P y),
  we would have the identity of indiscernibles (contragruence?),
  but only up to propositions, since P: a -> Type.
  Recall the general statement,
    idind: (forall f. f x = f y) -> x = y,
  where f: (x: a) -> b x for any a: Type and b: a -> Type.

  Note that we still can't prove extensionality for propositions,
    propext: (forall x. P x = Q x) -> P = Q
  even if P, Q: a -> Type.
-}

impl : ({P : a -> Type} -> P x = P y) -> x .=. y
impl refl = \px => rewrite sym $ refl {P} in px

contrag : ({P : a -> Type} -> P x = P y) -> x = y
contrag = LtoML . impl

-- For the next few bits we will need extensionality.
ext : ({x : a} -> f x = g x) -> f = g


-- Example: Proving an isomorphism.

-- This is essentially a CPS transformation of a
T : Type -> Type
T a = forall X. (a -> X) -> X

||| R is a relation between sets X and X'
||| k and k' are mappings from A to X and X'
||| t is a T A, which maps a function A -> X to X
||| Parametricity for T states that if (k a) R (k' a), then (t k) R (t k').
|||    A ---- k ---> X        1 --- t k --> X
|||    |             |        |             |
|||    |             |        |             |
||| If id            R, then  id            R
|||    |             |        |             |
|||    V             V        V             |
|||    A ---- k'---> X'       1 --- t k'--> X'
paramT : forall A, X, X'. (t : T A) -> (R : X -> X' -> Type) -> (k : A -> X) -> (k' : A -> X') ->
  (kR : {a : A} -> R (k a) (k' a)) -> R (t k) (t k')

-- A map from A to T A
i' : forall A. A -> T A
i' a k = k a

-- A map from T A to A
j' : forall A. T A -> A
j' t = t id

-- j is inverse to i
ji' : j' (i' a) = a
ji' = Refl

-- i is inverse to j when applied to k
-- Parametricity: if k a = k a then k (t {A} id) = t {X} k
ijExt' : forall A, X. {t : T A} -> {k : A -> X} -> i' (j' t) k = t k
ijExt' = paramT t (\a, x => k a = x) id k Refl

-- i is inverse to j
ij' : forall A. {t : T A} -> i' (j' t) = t
ij' = ext ijk
  where
    ijk : forall X. {k : A -> X} -> k (t Prelude.id) = t k
    ijk {k} = ijExt' {t} {k}


-- .=. ≃ =: Leibniz equality is isomorphic to M-L equality.

||| P, P' are predicates over A
||| R a is a relation between P a and P' a, and similarly for R b
||| Pa is a proof that if P a, then aeqb Pa is a proof of P b, and similarly for P'a
||| Parametricity for .=. states that if Pa Ra P'a then (aeqb Pa) Rb (aeqb P'a).
|||   Pa --- P= ---> Pb
|||   |              |
|||   |              |
|||   Ra             Rb
|||   |              |
|||   V              V
|||   P'a -- P'= --> P'b
paramL : forall A, a, b, P, P'. {aeqb : a .=. b} -> (R : {c : A} -> P c -> P' c -> Type) -> (Pa : P a) -> (P'a : P' a) ->
  R Pa P'a -> R (aeqb {P = P} Pa) (aeqb {P = P'} P'a)
