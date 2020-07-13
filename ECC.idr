import Shifted

%default total

-- ECC (Extended Calculus of Constructions)
-- With definitions and dependent conditionals

data Exp : Nat -> Type where
  Id      : Var k -> Exp k                    -- Variables (shifted names)
  Prop    : Exp k                             -- Prop (impredicative)
  Typ     : Nat -> Exp k                      -- Type_i
  Pi      : Exp k -> Exp (S k) -> Exp k       -- Dependent function types: Π(x:A).B
  Abs     : Exp k -> Exp (S k) -> Exp k       -- Functions: λ(x:A).B
  App     : Exp k -> Exp k -> Exp k           -- Applications: e e
  Sigma   : Exp k -> Exp (S k) -> Exp k       -- Dependent pair types: Σ(x:A).B
  Pair    : Exp k -> Exp k -> Exp k -> Exp k  -- Pairs: ⟨e, e⟩ as T
  Fst     : Exp k -> Exp k                    -- First projection: π₁ e
  Snd     : Exp k -> Exp k                    -- Second projection: π₂ e
  Boolean : Exp k                             -- Boolean type
  True    : Exp k                             -- Boolean true
  False   : Exp k                             -- Boolean false
  If      : Exp k -> Exp k -> Exp k -> Exp k  -- Dependent conditionals: if e then e else e
  Let     : Exp k -> Exp (S k) -> Exp k       -- Definitions: let x = e in e


-- GENERIC MAP

plus_comm_S : (n, m: Nat) -> S (n + m) = n + S m
plus_comm_S Z n = Refl
plus_comm_S (S n) m = rewrite plus_comm_S n m in Refl

pop : Exp (S (n + m)) -> Exp (n + S m)
pop e = rewrite sym $ plus_comm_S n m in e

push : Exp (n + S m) -> Exp (S (n + m))
push e = rewrite plus_comm_S n m in e

map : ({k: Nat} -> Var (n + k) -> Exp (m + k)) -> ({k: Nat} -> Exp (n + k) -> Exp (m + k))
map f (Id var)        = f var
map _ Prop            = Prop
map _ (Typ i)         = Typ i
map f (Pi a b)        = Pi    (map f a)  (push (map f (assert_smaller b (pop b))))
map f (Abs a e)       = Abs   (map f a)  (push (map f (assert_smaller e (pop e))))
map f (App e1 e2)     = App   (map f e1) (map f e2)
map f (Sigma a b)     = Sigma (map f a)  (push (map f (assert_smaller b (pop b))))
map f (Pair e1 e2 a)  = Pair  (map f e1) (map f e2) (map f a)
map f (Fst e)         = Fst   (map f e)
map f (Snd e)         = Snd   (map f e)
map _ Boolean         = Boolean
map _ True            = True
map _ False           = False
map f (If e1 e2 e3)   = If    (map f e1) (map f e2) (map f e3)
map f (Let e1 e2)     = Let   (map f e1) (push (map f (assert_smaller e2 (pop e2))))


-- PRIMITIVE SHIFTED NAMES OPERATIONS

open_exp : {k: Nat} -> Name -> Exp (S k) -> Exp k
open_exp a = map {n = S Z} {m = Z} (Id . open_var a)

close_exp : {k: Nat} -> Name -> Exp k -> Exp (S k)
close_exp a = map {n = Z} {m = S Z} (Id . close_var a)

wk_exp : {k: Nat} -> Exp k -> Exp (S k)
wk_exp = map {n = Z} {m = S Z} (Id . wk_var)

{-
  A note about bind:
  When replacing an identifier of type Exp k with the expression e,
  the type of e needs to be Exp k as well. To enforce this, we first
  assume that e's type is Exp Z, and then we wk k times on e so that
  its type becomes Exp k. This is safe to do, since wk only introduces
  unused bound variables.
  In wkk, because we destruct on the implicit variable k,
  it has to be non-erased, i.e. {k: Nat} instead of forall k.
  This means that it has to be non-erased in basically everything as well.
-}

wkk_exp : {k: Nat} -> Exp Z -> Exp k
wkk_exp {k = Z} e = e
wkk_exp {k = S k'} e = wk_exp (wkk_exp {k = k'} e)

bind_exp : {k: Nat} -> Exp Z -> Exp (S k) -> Exp k
bind_exp u = map {n = S Z} {m = Z} bind
where
  bind : {k: Nat} -> Var (S k) -> Exp k
  bind = (maybe (wkk_exp u) Id . bind_var)


-- DERIVED SHIFTED NAMES OPERATIONS

-- rename old new renames old to new by
-- turning old into a bound variable, then opening it as new
rename : {k: Nat} -> Name -> Name -> Exp k -> Exp k
rename old new = open_exp new . close_exp old

-- subst name u substitutes free variable name for u
-- in a capture-avoiding manner, since u gets shifted by wkk
subst : {k: Nat} -> Name -> Exp Z -> Exp k -> Exp k
subst name u = bind_exp u . close_exp name

-- shift name ensures that name is fresh by
-- introducing a new binding and then opening it as name
shift : {k: Nat} -> Name -> Exp k -> Exp k
shift name = open_exp name . wk_exp


-- PROPERTIES and LEMMAS

-- Theorem: Renaming a variable by itself should do nothing.
rename_refl : {a: Name} -> {x: Exp k} -> rename a a x = x

-- Theorem: Renaming should be transitive.
rename_trans : {a, b, c: Name} -> {x: Exp k} -> rename b c (rename a b x) = rename a c x

-- Theorem: Renaming a variable and then renaming it back should do nothing.
rename_symm : {a, b: Name} -> (x: Exp k) -> rename b a (rename a b x) = x

-- Theorem: Renaming then substituting should be the same as substituting the original variable.
subst_rename : {a, b: Name} -> {x: Exp Z} -> subst b (rename a b x) = subst a x

-- Theorem: Substituting an unused variable should do nothing.
subst_shift : {a: Name} -> {x: Exp Z} -> subst a (shift a x) = Just x

-- Theorem: Summoning free variable b after renaming from a is the same as summoning free variable a.
shift_rename : {a, b: Name} -> {x: Exp k} -> shift b (rename a b x) = shift a
