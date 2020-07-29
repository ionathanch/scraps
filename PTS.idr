{-
  https://prosecco.gforge.inria.fr/personal/hritcu/temp/snforcc.pdf
-}

import Shifted

%default total

data Sort = Typ | Kind

data Axiom : Sort -> Sort -> Type where
  TK : Axiom Typ Kind

data Rule : Sort -> Sort -> Sort -> Type where
  TTT : Rule Typ  Typ  Typ  -- terms depending on terms
  KTT : Rule Kind Typ  Typ  -- terms depending on types
  KKK : Rule Kind Kind Kind -- types depending on types
  TKK : Rule Typ  Kind Kind -- types depending on terms

data Expr : Nat -> Type where
  Id      : Var k -> Expr k                       -- Variables (shifted names)
  Srt     : Sort -> Expr k                        -- Sorts
  Pi      : Expr k -> Expr (S k) -> Expr k        -- Dependent function types: Π(x:A).B
  Abs     : Expr k -> Expr (S k) -> Expr k        -- Functions: λ(x:A).B
  App     : Expr k -> Expr k -> Expr k            -- Applications: e e
  Let     : Expr k -> Expr (S k) -> Expr k        -- Definitions: let x = e in e


Term Expr where
  unit = Id
  kmap f (Id var)        = f var
  kmap _ (Srt s)         = Srt s
  kmap f (Pi a b)        = Pi    (kmap f a)  (push (kmap f (assert_smaller b (pop b))))
  kmap f (Abs a e)       = Abs   (kmap f a)  (push (kmap f (assert_smaller e (pop e))))
  kmap f (App e1 e2)     = App   (kmap f e1) (kmap f e2)
  kmap f (Let e1 e2)     = Let   (kmap f e1) (push (kmap f (assert_smaller e2 (pop e2))))
-- We could give Let expressions type annotations, but we want to keep it as small as possible.

-- Make a variable out of a name.
toVar : Name -> Expr k
toVar name = Id (Free name)


-- ENVIRONMENTS

data Decl = Ass (Expr Z) | Def (Expr Z)

Env : Type
Env = Context Decl

data Declares : Env -> Var Z -> Expr Z -> Type where
  Assumes : has g x (Ass a) -> Declares g x a
  Defines : has g x (Def e) -> Declares g x a


-- REDUCTION, CONVERSION, EQUIVALENCE

data Red : Env -> Expr k -> Expr k -> Type where
  Delta : has g x (Def e) -> Red g (Id x) e
  Beta  : Red _ (App (Abs _ e) u) (bind_term u e)
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

  CongLet   : Conv g e1 e1' ->
              Conv (Cons (Cons g x (Ass a)) x (Def e1)) (open_term x e2) (open_term x e2') ->
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

data Types : Env -> Expr k1 -> Expr k2 -> Type where
  TId   : has g x (Ass a) ->
          ----------------
          Types g (Id x) a

  TSort : Axiom s1 s2 ->
          -------------------------
          Types g (Srt s1) (Srt s2)

  TPi   : Types g a (Srt s1) ->
          Types (Cons g x (Ass a)) (open_term x b) (Srt s2) ->
          Rule s1 s2 s3 ->
          -------------------------
          Types g (Pi a b) (Srt s3)

  TAbs  : Types g a (Srt s) ->
          Types (Cons g x (Ass a)) (open_term x e) (open_term x b) ->
          --------------------------
          Types g (Abs a e) (Pi a b)

  TApp  : Types g e1 (Pi a b) ->
          Types g e2 b ->
          ------------------------------------
          Types g (App e1 e2) (bind_term e2 b)

  TLet  : Types g e1 a ->
          Types (Cons (Cons g x (Ass a)) x (Def e1)) (open_term x e2) (open_term x b) ->
          ------------------------------------
          Types g (Let e1 e2) (bind_term e1 b)

  TConv : Types g e a ->
          Types g b (Srt s) ->
          Equiv g a b ->
          -----------
          Types g e b
