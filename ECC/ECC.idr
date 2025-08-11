import Shifted

%default total

-- ECC (Extended Calculus of Constructions)
-- With definitions and dependent conditionals

data Expr : Nat -> Type where
  Id      : Var k -> Expr k                       -- Variables (shifted names)
  Prop    : Expr k                                -- Prop (impredicative)
  Typ     : Nat -> Expr k                         -- Type_i
  Pi      : Expr k -> Expr (S k) -> Expr k        -- Dependent function types: Π(x:A).B
  Abs     : Expr k -> Expr (S k) -> Expr k        -- Functions: λ(x:A).e
  App     : Expr k -> Expr k -> Expr k            -- Applications: e e
  Sigma   : Expr k -> Expr (S k) -> Expr k        -- Dependent pair types: Σ(x:A).B
  Pair    : Expr k -> Expr k -> Expr k -> Expr k  -- Pairs: ⟨e, e⟩ as T
  Fst     : Expr k -> Expr k                      -- First projection: π₁ e
  Snd     : Expr k -> Expr k                      -- Second projection: π₂ e
  Boolean : Expr k                                -- Boolean type
  True    : Expr k                                -- Boolean true
  False   : Expr k                                -- Boolean false
  If      : Expr k -> Expr k -> Expr k -> Expr k  -- Dependent conditionals: if e then e else e
  Let     : Expr k -> Expr (S k) -> Expr k        -- Definitions: let x = e in e

Term Expr where
  unit = Id
  kmap f (Id var)        = f var
  kmap _ Prop            = Prop
  kmap _ (Typ i)         = Typ i
  kmap f (Pi a b)        = Pi    (kmap f a)  (push (kmap f (assert_smaller b (pop b))))
  kmap f (Abs a e)       = Abs   (kmap f a)  (push (kmap f (assert_smaller e (pop e))))
  kmap f (App e1 e2)     = App   (kmap f e1) (kmap f e2)
  kmap f (Sigma a b)     = Sigma (kmap f a)  (push (kmap f (assert_smaller b (pop b))))
  kmap f (Pair e1 e2 a)  = Pair  (kmap f e1) (kmap f e2) (kmap f a)
  kmap f (Fst e)         = Fst   (kmap f e)
  kmap f (Snd e)         = Snd   (kmap f e)
  kmap _ Boolean         = Boolean
  kmap _ True            = True
  kmap _ False           = False
  kmap f (If e1 e2 e3)   = If    (kmap f e1) (kmap f e2) (kmap f e3)
  kmap f (Let e1 e2)     = Let   (kmap f e1) (push (kmap f (assert_smaller e2 (pop e2))))
-- We could give Let expressions type annotations, but we want to keep it as small as possible.

-- Make a variable out of a name.
toVar : Name -> Expr k
toVar name = Id (Free name)


-- ENVIRONMENTS

data Decl = Ass (Expr Z) | Def (Expr Z)

Env : Type
Env = Context Decl

-- Note that definitions in the environment aren't typed.
-- This is because Let expressions aren't type annotated,
-- So during conversion, there's no type to stick into
-- the environment, not unless we provide a proof that
-- the bound term has a certain type.
data Declares : Env -> Var Z -> Expr Z -> Type where
  Assumes : has g x (Ass a) -> Declares g x a
  Defines : has g x (Def e) -> Declares g x a


-- REDUCTION, CONVERSION, EQUIVALENCE

data Red : Env -> Expr k -> Expr k -> Type where
  Delta : has g x (Def e) -> Red g (Id x) e
  Beta  : Red _ (App (Abs _ e) u) (bind_term u e)
  Pi1   : Red _ (Fst (Pair e1 _ _)) e1
  Pi2   : Red _ (Snd (Pair _ e1 _)) e2
  Iota1 : Red _ (If True e1 _) e1
  Iota2 : Red _ (If False _ e2) e2
  Zeta  : Red _ (Let u e) (bind_term u e)

data Conv : Env -> Expr k -> Expr k -> Type where
  ConvRefl  : Conv _ e e

  ConvTrans : Red g e e' ->
              Conv g e' e'' ->
              ----------------
              Conv g e e''

  CongPi    : Conv g a a' ->
              Conv (Cons g x (Ass a)) (open_term x b) (open_term x b') ->
              --------------------------
              Conv g (Pi a b) (Pi a' b')

  CongAbs   : Conv g a a' ->
              Conv (Cons g x (Ass a)) (open_term x e) (open_term x e') ->
              ----------------------------
              Conv g (Abs a e) (Abs a' e')

  CongApp   : Conv g e1 e1' ->
              Conv g e2 e2' ->
              --------------------------------
              Conv g (App e1 e2) (App e1' e2')

  CongSigma : Conv g a a' ->
              Conv (Cons g x (Ass a)) (open_term x b) (open_term x b') ->
              --------------------------------
              Conv g (Sigma a b) (Sigma a' b')

  CongPair  : Conv g e1 e1' ->
              Conv g e2 e2' ->
              Conv g a a' ->
              ----------------------------------------
              Conv g (Pair e1 e2 a) (Pair e1' e2' a')

  CongFst   : Conv g e e' ->
              -----------------------
              Conv g (Fst e) (Fst e')

  CongSnd   : Conv g e e' ->
              -----------------------
              Conv g (Snd e) (Snd e')

  CongIf    : Conv g e1 e1' ->
              Conv g e2 e2' ->
              Conv g e3 e3' ->
              -------------------------------------
              Conv g (If e1 e2 e3) (If e1' e2' e3')

  CongLet   : Conv g e1 e1' ->
              Conv (Cons g x (Def e1)) (open_term x e2) (open_term x e2') ->
              --------------------------------
              Conv g (Let e1 e2) (Let e1' e2')

data Equiv : Env -> Expr k -> Expr k -> Type where
  EquivConv : Conv g e1 e ->
              Conv g e2 e ->
              -------------
              Equiv g e1 e2

  EquivEta1 : Conv g e1 (Abs a e) ->
              Conv g e2 e2' ->
              Equiv (Cons g x (Ass a)) (open_term x e) (App e2' (toVar x)) ->
              -------------
              Equiv g e1 e2

  EquivEta2 : Conv g e1 e1' ->
              Conv g e2 (Abs a e) ->
              Equiv (Cons g x (Ass a)) (App e1' (toVar x)) (open_term x e) ->
              -------------
              Equiv g e1 e2


-- TYPING

data Subtypes : Env -> Expr k -> Expr k -> Type where
  STEquiv : Equiv g e1 e2 ->
            ---------------
            Subtypes g e1 e2

  STTrans : Subtypes g a b ->
            Subtypes g b c ->
            --------------
            Subtypes g a c

  STProp  : Subtypes _ Prop (Typ Z)

  STCum   : Subtypes _ (Typ i) (Typ (S i))

  STPi    : Equiv g a1 a2 ->
            Subtypes (Cons g x (Ass a2)) (open_term x b1) (open_term x b2) ->
            --------------------------------
            Subtypes g (Pi a1 b1) (Pi a2 b2)

  STSig   : Subtypes a a1 a2 ->
            Subtypes (Cons g x (Ass a2)) (open_term x b1) (open_term x b2) ->
            --------------------------------------
            Subtypes g (Sigma a1 b1) (Sigma a2 b2)

data Types : Env -> Expr k1 -> Expr k2 -> Type where
  TId : has g x (Ass a) ->
        ----------------
        Types g (Id x) a
