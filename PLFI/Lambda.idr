import Decidable.Equality
import Data.DPair
import NotDec

%default total

----------------
---- SYNTAX ----
----------------

Id : Type
Id = String

-- Curry-style lambda calculus with Peano naturals and fixpoints
data Term : Type where
  Var  : Id -> Term                           -- Variables: x
  Lam  : Id -> Term -> Term                   -- Lambda abstractions: λx.e
  App  : Term -> Term -> Term                 -- Applications: e e
  Fix  : Id -> Term -> Term                   -- Fixpoints: μx.e
  Zero : Term                                 -- Natural: zero
  Succ : Term -> Term                         -- Natural: successor
  Case : Term -> Term -> Id -> Term -> Term   -- Case: case e of [zero => e₁ | succ n => e₂]

----------------
---- VALUES ----
----------------

-- Irreducible values in weak normal form
data Value : Term -> Type where
  VLam  : Value (Lam x e)
  VZero : Value Zero
  VSucc : Value v -> Value (Succ v)

----------------------
---- SUBSTITUTION ----
----------------------

-- NOT capture-avoiding substitution
subst : Term -> Id -> Term -> Term
subst (Var x) y v with (decEq x y)
  subst (Var x) y v | Yes _ = v
  subst (Var x) y v | No  _ = Var x
subst (Lam x e) y v with (decEq x y)
  subst (Lam x e) y v | Yes _ = Lam x e
  subst (Lam x e) y v | No  _ = Lam x (subst e y v)
subst (App e1 e2) y v = App (subst e1 y v) (subst e2 y v)
subst (Fix x e) y v with (decEq x y)
  subst (Fix x e) y v | Yes _ = Fix x e
  subst (Fix x e) y v | No  _ = Fix x (subst e x v)
subst Zero y v = Zero
subst (Succ n) y v = Succ (subst n y v)
subst (Case e e1 x e2) y v with (decEq x y)
  subst (Case e e1 x e2) y v | Yes _ = Case (subst e y v) (subst e1 y v) x e2
  subst (Case e e1 x e2) y v | No  _ = Case (subst e y v) (subst e1 y v) x (subst e2 y v)

-------------------
---- REDUCTION ----
-------------------

-- Reduction rules combined with compatible closure rules
data Red : Term -> Term -> Type where
  -- Conventional reduction rules
  Beta  : Value v -> Red (App (Lam x e) v) (subst e x v)
  Mu    : Red (Fix x e) (subst e x (Fix x e))
  IotaZ : Red (Case Zero e1 x e2) e1
  IotaS : Value v -> Red (Case (Succ v) e1 x e2) (subst e2 x v)

  -- Compatible closure rules
  XiApp1 : Red e1 e1' ->
           ----------------------------
           Red (App e1 e2) (App e1' e2)

  XiApp2 : Value v ->
           Red e2 e2' ->
           --------------------------
           Red (App v e2) (App v e2')

  XiSucc : Red n n' ->
           ----------------------
           Red (Succ n) (Succ n')

  XiCase : Red e e' ->
           --------------------------------------
           Red (Case e e1 x e2) (Case e' e1 x e2)

----------------------------
---- REFL/TRANS CLOSURE ----
----------------------------

-- Multistep reduction as a chain of reductions
infix 5 ->>
data (->>) : Term -> Term -> Type where
  End : e ->> e
  Chain : Red e1 e2 ->
          e2 ->> e3 ->
          ---------
          e1 ->> e3

-- Multistep reduction as the reflexive, transitive closure
infix 5 ->>*
data (->>*) : Term -> Term -> Type where
  Step  : Red e1 e2 ->
          ---------
          e1 ->>* e2

  Refl  : e ->>* e
  
  Trans : e1 ->>* e2 ->
          e2 ->>* e3 ->
          ---------
          e1 ->>* e3

multistepTo : (e1 ->> e2) -> (e1 ->>* e2)
multistepTo End = Refl
multistepTo (Chain red ms) = Trans (Step red) (multistepTo ms)

unravel : (e1 ->> e2) -> (e2 ->> e3) -> (e1 ->> e3)
unravel End ms = ms
unravel (Chain red ms1) ms2 = Chain red (unravel ms1 ms2)

multistepFrom : (e1 ->>* e2) -> (e1 ->> e2)
multistepFrom Refl = End
multistepFrom (Step red) = Chain red End
multistepFrom (Trans ms1 ms2) = unravel (multistepFrom ms1) (multistepFrom ms2)

-- (->>) embeds into (->>*)...
multistepFromTo : (ms : e1 ->> e2) -> multistepFrom (multistepTo ms) = ms
multistepFromTo End = Refl
multistepFromTo (Chain red ms) = rewrite multistepFromTo ms in Refl

-- ...but (->>*) does not embed into (->>)
-- because we can't simplify (Trans ms Refl) to ms
transReflLeft  : (ms : e1 ->>* e2) -> Trans Refl ms = ms
transReflRight : (ms : e1 ->>* e2) -> Trans ms Refl = ms

multiUnravel : (ms1 : e1 ->>* e2) -> (ms2 : e2 ->>* e3) ->
  multistepTo (unravel (multistepFrom ms1) (multistepFrom ms2)) =
    Trans (multistepTo (multistepFrom ms1)) (multistepTo (multistepFrom ms2))
multiUnravel Refl ms = rewrite transReflLeft (multistepTo (multistepFrom ms)) in Refl
multiUnravel (Step red) ms = rewrite transReflRight (Step red) in Refl
multiUnravel (Trans ms1 ms2) ms = ?transMultiUnravel

multistepToFrom : (ms : e1 ->>* e2) -> multistepTo (multistepFrom ms) = ms
multistepToFrom Refl = Refl
multistepToFrom (Step red) =
  rewrite transReflRight (Step red) in Refl
multistepToFrom (Trans ms1 ms2) =
  rewrite multiUnravel ms1 ms2 in
  rewrite multistepToFrom ms1 in
  rewrite multistepToFrom ms2 in Refl

--------------------
---- CONFLUENCE ----
--------------------

-- Reduction is deterministic, in that for every redex,
-- there is only one way to reduce it
-- This proof is incomplete, but because of the impossible branches,
-- the typechecker doesn't notice the rest of the missing cases
deterministic : Red e e1 -> Red e e2 -> e1 = e2
deterministic (Beta _) (Beta _) = Refl
deterministic Mu Mu = Refl
deterministic IotaZ IotaZ = Refl
deterministic (IotaS _) (IotaS _) = Refl
deterministic (XiApp1 red1) (XiApp1 red2) = rewrite deterministic red1 red2 in Refl
deterministic (XiApp2 _ red1) (XiApp2 _ red2) = rewrite deterministic red1 red2 in Refl
deterministic (XiSucc red1) (XiSucc red2) = rewrite deterministic red1 red2 in Refl
deterministic (XiCase red1) (XiCase red2) = rewrite deterministic red1 red2 in Refl
deterministic (XiApp1 _) (XiApp2 VLam _) impossible
deterministic (XiApp1 _) (XiApp2 VZero _) impossible

-- If a term reduces to two terms then those two terms multistep to the same term
diamond : {e2 : Term} -> Red e e1 -> Red e e2 -> Exists (\e' => (e1 ->> e', e2 ->> e'))
diamond {e2} red1 red2 = rewrite deterministic red1 red2 in Evidence e2 (End, End)

-- If a term multisteps to two terms then those two terms multistep to the same term
-- There's some more problems with implicit variables in this proof
confluence : {e, e1, e2 : Term} -> (e ->> e1) -> (e ->> e2) -> Exists (\e' => (e1 ->> e', e2 ->> e'))
confluence {e} End End = Evidence e (End, End)
confluence {e2} End (Chain red ms) = Evidence e2 (Chain red ms, End)
confluence {e1} (Chain red ms) End = Evidence e1 (End, Chain red ms)
confluence {e} (Chain red1 ms1) (Chain red2 ms2) = ?conflChain {-
  let Evidence e' (ms1', ms2') = diamond red1 red2 in
  let Evidence e1 (ms1'', _) = confluence ms1' ms1 in
  let Evidence e2 (ms2'', _) = confluence ms2' ms2 in
  let Evidence e'' (ms1''', ms2''') = confluence ms1'' ms2'' in
  Evidence e'' (unravel (unravel ms1' ms1'') ms1''',
                unravel (unravel ms2' ms2'') ms2''') -}

-------------------------
---- TYPING CONTEXTS ----
-------------------------

-- Function types and naturals
data Typ : Type where
  Fun : Typ -> Typ -> Typ
  N : Typ

-- Context of bindings
data Context : Type where
  Empty : Context
  Cons  : Context -> Id -> Typ -> Context

contextTo : Context -> List (Id, Typ)
contextTo Empty = Nil
contextTo (Cons ctxt id typ) = (id, typ) :: (contextTo ctxt)

contextFrom : List (Id, Typ) -> Context
contextFrom Nil = Empty
contextFrom ((id, typ) :: rest) = Cons (contextFrom rest) id typ

-- Contexts are isomorphic to List (Id, Typ)

contextToFrom : (lst : List (Id, Typ)) -> contextTo (contextFrom lst) = lst
contextToFrom Nil = Refl
contextToFrom ((id, typ) :: rest) = rewrite contextToFrom rest in Refl

contextFromTo : (ctxt : Context) -> contextFrom (contextTo ctxt) = ctxt
contextFromTo Empty = Refl
contextFromTo (Cons ctxt id typ) = rewrite contextFromTo ctxt in Refl

-- Lookup binding in context
data In : Context -> Id -> Typ -> Type where
  This : In (Cons ctxt id typ) id typ
  That : Not (x = y) -> In ctxt x typ -> In (Cons ctxt y typ') x typ

-- Lookup "smart" constructor for That using proof by reflection
That' : {x, y : Id} -> {xneqy : T (not (erase (decEq x y)))} -> In ctxt x typ -> In (Cons ctxt y typ') x typ
That' {x} {y} {xneqy} inCtxt = That (toWitnessFalse xneqy) inCtxt

-- Lookup is injective
inInjective : In ctxt x a -> In ctxt x b -> a = b
inInjective This This = Refl
inInjective This (That xneqy inCtxt) = void (xneqy Refl)
inInjective (That xneqy inCtxt) This = void (xneqy Refl)
inInjective (That _ inCtxt1) (That _ inCtxt2) = inInjective inCtxt1 inCtxt2

--------------------------
---- TYPING JUDGEMENT ----
--------------------------

data Types : Context -> Term -> Typ -> Type where
  TVar : In ctxt x a ->
         --------------------
         Types ctxt (Var x) a

  TLam : Types (Cons ctxt x a) e b ->
         ------------------------------
         Types ctxt (Lam x e) (Fun a b)

  TApp : Types ctxt e1 (Fun a b) ->
         Types ctxt e2 a ->
         ------------------------
         Types ctxt (App e1 e2) b

  TFix : Types (Cons ctxt x a) e a ->
         ----------------------
         Types ctxt (Fix x e) a

  TZero : Types ctxt Zero N

  TSucc : Types ctxt n N ->
          ---------------------
          Types ctxt (Succ n) N

  TCase : Types ctxt e N ->
          Types ctxt e1 a ->
          Types (Cons ctxt x N) e2 a ->
          -----------------------------
          Types ctxt (Case e e1 x e2) a

-- Proof that (App Zero (Succ Zero)) is not typeable
nope1 : Not (Types ctxt (App Zero (Succ Zero)) a)
nope1 (TApp _ _) impossible

-- Proof that (Lam x (App x x)) is not typeable
nope2 : Not (Types ctxt (Lam x (App (Var x) (Var x))) a)
nope2 (TLam (TApp (TVar in1) (TVar in2))) = contradiction (inInjective in1 in2)
  where
    contradiction : Not (Fun a b = a)
    contradiction impossible
