{-
  https://prosecco.gforge.inria.fr/personal/hritcu/temp/snforcc.pdf
-}

import Data.Fin
import Data.Vect

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
  Id      : Fin k -> Expr k                           -- Variables (de Bruijn indices)
  Srt     : Sort -> Expr k                            -- Sorts
  Pi      : Expr k -> Expr (S k) -> Expr k            -- Dependent function types: Π(x:A).B
  Abs     : Expr k -> Expr (S k) -> Expr k            -- Functions: λ(x:A).e
  App     : Expr k -> Expr k -> Expr k                -- Applications: e e
  Let     : Expr k -> Expr k -> Expr (S k) -> Expr k  -- Definitions: let x = e in e

eWeaken : Expr k -> Expr (S k)
eWeaken (Id k)       = Id (weaken k)
eWeaken (Srt s)      = Srt s
eWeaken (Pi a b)     = Pi  (eWeaken a) (eWeaken b)
eWeaken (Abs a e)    = Abs (eWeaken a) (eWeaken e)
eWeaken (App e e')   = App (eWeaken e) (eWeaken e')
eWeaken (Let a e e') = Let (eWeaken a) (eWeaken e) (eWeaken e')


-- ENVIRONMENTS

data Decl : Nat -> Type where
  Ass : Expr k -> Decl k
  Def : Expr k -> Expr k -> Decl k

dWeaken : Decl k -> Decl (S k)
dWeaken (Ass t) = Ass (eWeaken t)
dWeaken (Def e t) = Def (eWeaken e) (eWeaken t)

Env : Nat -> Type
Env k = Vect k (Decl k)

infix 5 ::
(::) : Env k -> Decl k -> Env (S k)
g :: e = map dWeaken (Vect.(::) e g)

lookup : Fin k -> Env k -> Expr k
lookup x g = case index x g of
  Ass   t => t
  Def _ t => t


-- SUBSTITUTION

subst : Env k -> Fin k -> Expr k
subst g x = case index x g of
  Def e _ => e
  Ass   _ => (Id x)


-- TYPING

data Types : Env k -> Expr k -> Expr k -> Type where
  TId   : ---------------------------
          Types g (Id x) (lookup x g)

  TSort : Axiom s1 s2 ->
          -------------------------
          Types g (Srt s1) (Srt s2)

  TPi   : Types g a (Srt s1) ->
          Types (g :: (Ass a)) b (Srt s2) ->
          Rule s1 s2 s3 ->
          -------------------------
          Types g (Pi a b) (Srt s3)

  TAbs  : Types g a (Srt s) ->
          Types (g :: (Ass a)) e b ->
          --------------------------
          Types g (Abs a e) (Pi a b)

  TApp  : Types g e1 (Pi a b) ->
          Types g e2 a ->
          --------------------------------
          Types g (App e1 e2) (Let a e1 b)

  TLet  : Types g e1 a ->
          Types (g :: (Def e1 a)) e2 b ->
          ----------------------------------
          Types g (Let a e1 e2) (Let a e1 b)

  TConv : Types g e a ->
          Types g b (Srt s) ->
          Equiv g a b ->
          -----------
          Types g e b

{-

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

-}
