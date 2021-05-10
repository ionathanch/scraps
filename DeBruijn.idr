%default total

Idx: Type
Idx = Nat

data Term: Type where
  Var: Idx -> Term
  Pi:  Term -> Term -> Term
  Lam: Term -> Term -> Term
  App: Term -> Term -> Term
  Let: Term -> Term -> Term -> Term
  Set: Term

shift: Term -> Term
shift term = shift' Z term
  where
    shift': Nat -> Term -> Term
    shift' n (Var i) = if i >= n then Var (i + 1) else Var i
    shift' n (Pi t t') = Pi (shift' n t) (shift' (S n) t')
    shift' n (Lam t e) = Lam (shift' n t) (shift' (S n) e)
    shift' n (App e1 e2) = App (shift' n e1) (shift' n e2)
    shift' n (Let t e1 e2) = Let (shift' n t) (shift' n e1) (shift' (S n) e2)
    shift' n Set = Set

substVar: Idx -> Idx -> Idx
substVar Z Z = Z
substVar Z (S i) = i
substVar n Z = n
substVar (S n) (S i) = substVar n i

subst: Term -> Term -> Term
subst body e = subst' Z body e
  where
    subst': Nat -> Term -> Term -> Term
    subst' n (Var i) e = Var (substVar n i)
    subst' n (Pi t t') e = Pi (subst' n t e) (subst' (S n) t' (shift e))
    subst' n (Lam t e') e = Lam (subst' n t e) (subst' (S n) e' (shift e))
    subst' n (App e1 e2) e = App (subst' n e1 e) (subst' n e2 e)
    subst' n (Let t e1 e2) e = Let (subst' n t e) (subst' n e1 e) (subst' (S n) e2 (shift e))
    subst' n Set e = Set

data Decl: Type where
  Ass: Term -> Decl
  Def: Term -> Term -> Decl

data Env: Type where
  Nil: Env
  (::): Decl -> Env -> Env

data In: Idx -> Term -> Env -> Type where
  Here: forall t, env.
        In Z t (Ass t :: env)
  There: forall i, t, d, env.
        In i t env ->
        In (S i) t (d :: env)

data Is: Idx -> Term -> Env -> Type where
  This: forall t, e, env.
        Is Z e (Def t e :: env)
  That: forall i, e, d, env.
        Is i e env ->
        Is (S i) e (d :: env)

data Conv: Env -> Term -> Term -> Type where
  Refl: forall e, env. Conv env e e
  Sym: forall e1, e2, env. Conv env e1 e2 -> Conv env e2 e1
  Trans: forall e1, e2, e3, env. Conv env e1 e2 -> Conv env e2 e3 -> Conv env e1 e3
  CongPi: forall t1, t1', t2, t2', env.
        Conv env t1 t1' ->
        Conv env t2 t2' ->
        --------------------------------
        Conv env (Pi t1 t2) (Pi t1' t2')
  CongLam: forall t, t', e, e', env.
        Conv env t t' ->
        Conv env e e' ->
        ------------------------------
        Conv env (Lam t e) (Lam t' e')
  CongApp: forall e1, e1', e2, e2', env.
        Conv env e1 e1' ->
        Conv env e2 e2' ->
        ----------------------------------
        Conv env (App e1 e1') (App e2 e2')
  CongLet: forall t, t', e1, e1', e2, e2', env.
        Conv env t t' ->
        Conv env e1 e1' ->
        Conv env e2 e2' ->
        ---------------------------------------
        Conv env (Let t e1 e2) (Let t' e1' e2')
  Eta:  forall t, e1, e2, env.
        Conv (Ass t :: env) e1 (App (shift e2) (Var Z)) ->
        ----------------------
        Conv env (Lam t e1) e2
  Beta: forall t, e, e', env.
        ----------------------------------------
        Conv env (App (Lam t e) e') (subst e e')
  Zeta: forall t, e, e', env.
        ----------------------------------
        Conv env (Let t e' e) (subst e e')
  Delta: forall e, env.
        Is i e env ->
        ------------------
        Conv env (Var i) e

data Types: Env -> Term -> Term -> Type where
  TVar: forall i, t, env.
        In i t env ->
        -------------------
        Types env (Var i) t
  TPi:  forall x, t, t', env.
        Types env t Set ->
        Types (Ass t :: env) t' Set ->
        -----------------------
        Types env (Pi t t') Set
  TLam: forall x, t, t', e, env.
        Types env t Set ->
        Types (Ass t :: env) e t' ->
        -----------------------------
        Types env (Lam t e) (Pi t t')
  TApp: forall x, e1, e2, t, t', env.
        Types env e1 (Pi t t') ->
        Types env e2 t ->
        -----------------------------------
        Types env (App e1 e2) (Let t e1 t')
  TLet: forall x, t, t', e1, e2, env.
        Types env t Set ->
        Types env e1 t ->
        Types (Def t e1 :: env) e2 t' ->
        -------------------------------------
        Types env (Let t e1 e2) (Let t e1 t')
  TConv: forall e, t, t', env.
        Types env e t ->
        Conv env t t' ->
        --------------
        Types env e t'

substLemma: forall e, e', t, t', env. Types (Def t' e' :: env) e t -> Types env (subst e e') t
convLemma: forall e1, e2, e, t, env. Conv (Def t e :: env) e1 e2 -> Conv env (subst e1 e) (subst e2 e)
