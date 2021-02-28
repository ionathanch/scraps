%default total

Id: Type

data Term: Type where
  Var: Id -> Term
  Pi: Id -> Term -> Term -> Term
  Lam: Id -> Term -> Term -> Term
  App: Term -> Term -> Term
  Let: Id -> Term -> Term -> Term -> Term
  Set: Term

subst: Term -> Id -> Term -> Term
subst e x e' = ? -- Left as an exercise for the reader.

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

  data Is: Id -> Term -> Env -> Type where
    This: forall x, e, t, env, types.
          Is x t (Def x t e env types)
    AThat: forall x, x', t, t', env, types.
          Is x t env ->
          Is x t (Ass x' t' env types)
    DThat: forall x, x', t, t', e', env, types.
          Is x t env ->
          Is x t (Def x' t' e' env types)

  data Conv: Env -> Term -> Term -> Type where
    Refl: forall e, env. Conv env e e
    Sym: forall e1, e2, env. Conv env e1 e2 -> Conv env e2 e1
    Trans: forall e1, e2, e3, env. Conv env e1 e2 -> Conv env e2 e3 -> Conv env e1 e3
    CongPi: forall x, t1, t1', t2, t2', env.
          Conv env t1 t1' ->
          Conv env t2 t2' ->
          ------------------------------------
          Conv env (Pi x t1 t2) (Pi x t1' t2')
    CongLam: forall x, t, t', e, e', env.
          Conv env t t' ->
          Conv env e e' ->
          ----------------------------------
          Conv env (Lam x t e) (Lam x t' e')
    CongApp: forall e1, e1', e2, e2', env.
          Conv env e1 e1' ->
          Conv env e2 e2' ->
          ----------------------------------
          Conv env (App e1 e1') (App e2 e2')
    CongLet: forall x, t, t', e1, e1', e2, e2', env.
          Conv env t t' ->
          Conv env e1 e1' ->
          Conv env e2 e2' ->
          -------------------------------------------
          Conv env (Let x t e1 e2) (Let x t' e1' e2')
    Beta: forall x, t, e, e', env.
          --------------------------------------------
          Conv env (App (Lam x t e) e') (subst e x e')
    Zeta: forall x, t, e, e', env.
          --------------------------------------
          Conv env (Let x t e e') (subst e x e')
    Delta: forall x, e, env.
          Is x e env ->
          ------------------
          Conv env (Var x) e

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
