{-
  Some properties about equalities and isomorphisms.
  Taken mostly from https://plfa.github.io/Equality/ and https://plfa.github.io/Isomorphism/
  The isomorphism examples are from "≐≃≡: Leibniz equality is isomorphic to Martin-Löf identity, parametrically": https://doi.org/10.1017/S0956796820000155
-}

%default total

-- Properties of Martin-Löf equality.
-- `sym`, `trans`, and `cong` are already defined in Prelude.
sym' : x = y -> y = x
sym' Refl = Refl

trans' : x = y -> y = z -> x = z
trans' Refl Refl = Refl

-- Generalized congruence over the functions
public export
congG : x = y -> f = g -> f x = g y
congG Refl Refl = Refl

-- Indiscernibility of identicals, i.e. congruence
-- It could probably also be written using congG,
-- but this proof is far shorter and cleaner.
cong' : x = y -> (forall f. f x = f y)
cong' Refl = Refl

-- This is also the indiscernibility of identicals,
-- where the property applied is P(f) = f x.
public export
congApp : f = g -> f x = g x
congApp = congG Refl

{-
  The converse of congruence is the identity of indiscernibles:
    idind: (forall f. f x = f y) -> x = y
  A related notion is functional extensionality (the converse of congApp):
    ext: (forall x. f x = g x) -> f = g
  I don't think these can be proven.
-}

public export
subst : forall f. x = y -> f x -> f y
subst Refl fx = fx

-- Like congApp, we can also prove this as
--    substapp = subst {f = \f => f x}
public export
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


-- We prove that Martin-Löf equality and Leibniz equality are functionally equivalent.

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

export
contrag : ({P : a -> Type} -> P x = P y) -> x = y
contrag = LtoML . impl


-- Properties of isomorphisms.

infix 9 =~=
public export
record (=~=) A B where
  constructor mkIso
  to : A -> B
  from : B -> A
  fromTo : forall x. from (to x) = x
  toFrom : forall y. to (from y) = y

public export
isoRefl : forall A. A =~= A
isoRefl = mkIso (\x => x) (\y => y) Refl Refl

public export
isoSym : forall A, B. A =~= B -> B =~= A
isoSym ab = mkIso ab.from ab.to ab.toFrom ab.fromTo

public export
isoTrans : forall A, B, C. A =~= B -> B =~= C -> A =~= C
isoTrans ab bc = mkIso (\x => bc.to (ab.to x)) (\y => ab.from (bc.from y)) ft tf
  where
    ft : forall x. ab.from (bc.from (bc.to (ab.to x))) = x
    ft {x} =
      rewrite bc.fromTo {x = (ab.to x)} in
      rewrite ab.fromTo {x} in Refl
    tf : forall y. bc.to (ab.to (ab.from (bc.from y))) = y
    tf {y} =
      rewrite ab.toFrom {y = (bc.from y)} in
      rewrite bc.toFrom {y} in Refl


-- For the next few bits we will need extensionality.
ext : ({x : a} -> f x = g x) -> f = g


-- Example: A is isomorphic to (forall X. (A -> X) -> X).

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
    ijk : forall X. {k : A -> X} -> k (j' t) = t k
    ijk {k} = ijExt' {t} {k}

-- The isomorphism from A to T A.
-- TODO: Fix implicit variables.
isoT : forall A. A =~= T A
isoT = mkIso i' j' ji' ij'


-- Example: Leibniz equality is isomorphic to M-L equality.

||| P, P' are predicates over A
||| R a is a relation between P a and P' a, and similarly for R b
||| If Pa is a proof of P a, then aeqb Pa is a proof of P b, and similarly for P'a
||| Parametricity for .=. states that if Pa Ra P'a then (aeqb Pa) Rb (aeqb P'a).
|||   Pa --- aeqb ---> Pb
|||   |                |
|||   |                |
|||   Ra               Rb
|||   |                |
|||   V                V
|||   P'a -- aeqb ---> P'b
paramL : forall A, a, b, P, P'. (aeqb : a .=. b) -> (R : {c : A} -> P c -> P' c -> Type) -> (Pa : P a) -> (P'a : P' a) ->
  R Pa P'a -> R (aeqb {P = P} Pa) (aeqb {P = P'} P'a)

-- MLtoL from above
i : a = b -> a .=. b
i Refl pa = pa

-- LtoML from above
j : a .=. b -> a = b
j aeqb = aeqb {P = \c => a = c} Refl

-- TODO: The type checker complains about implicit variables P
-- in the following signatures for ji, ijExt, and ij...

-- j is inverse to i
-- ji : {refl : a = b} -> j (i refl {P}) = refl
-- ji = Refl

-- i is inverse to j
-- ijExt : forall P. {aeqb : a .=. b} -> {Pa : P a} -> i (j aeqb) Pa = aeqb Pa
-- ijExt = paramL aeqb ?R Refl Pa Refl

-- ij : {aeqb : a .=. b} -> i (j aeqb) = aeqb
-- ij = ext ijk
--   where
--     ijk : forall P. {Pa : P a} -> Pa (j aeqb) = aeqb Pa
--     ijk {Pa} = ijExt' {aeqb} {Pa}

-- The isomorphism from .=. to =.
-- isoL : forall a, b. (a = b) =~= (a .=. b)
-- isoL = mkIso i j ij ji
