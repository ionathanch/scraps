%default total

Id: Type

data Term: Type where
  Var: Id -> Term
  Pi: Id -> Term -> Term -> Term
  Lam: Id -> Term -> Term -> Term
  App: Term -> Term -> Term
  Let: Id -> Term -> Term -> Term -> Term
  Set: Term

mutual  
  data Env: Type where
    Nil: Env
    Ass: (x: Id) -> (t: Term) -> (env: Env) -> Types env t Set -> Env
    Def: (x: Id) -> (t, e: Term) -> (env: Env) -> Types env e t -> Env

  data In: Id -> Term -> Env -> Type where
    Here: forall x, t, env, types.
          In x t (Ass x t env types)
    AThere: forall x, x', t, t', env, types.
          In x t env ->
          In x t (Ass x' t' env types)
    DThere: forall x, x', t, t', e', env, types.
          In x t env ->
          In x t (Def x' t' e' env types)
  
  data Conv: Env -> Term -> Term -> Type where
    {- Left as an exercise for the reader. -}

  data Types: Env -> Term -> Term -> Type where
    TVar: forall x, t, env.
          In x t env ->
          -------------------
          Types env (Var x) t
    TPi:  forall x, t, t', env.
          (tSet: Types env t Set) ->
          Types (Ass x t env tSet) t' Set ->
          --------------------------
          Types env (Pi x t t') Set
    TLam: forall x, t, t', e, env.
          (tSet: Types env t Set) ->
          Types (Ass x t env tSet) e t' ->
          ---------------------------------
          Types env (Lam x t e) (Pi x t t')
    TApp: forall x, e1, e2, t, t', env.
          Types env e1 (Pi x t t') ->
          Types env e2 t ->
          -------------------------------------
          Types env (App e1 e2) (Let x t e1 t')
    TLet: forall x, t, t', e1, e2, env.
          (tSet: Types env t Set) ->
          (e1t: Types (Ass x t env tSet) e1 t) ->
          Types (Def x t e1 (Ass x t env tSet) e1t) e2 t' ->
          -------------------------------------
          Types env (Let x t e1 e2) (Let x t e1 t')
    TConv: forall e, t, t', env.
          Types env e t ->
          Conv env t t' ->
          --------------
          Types env e t'
