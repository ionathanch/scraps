{-
  An implementation of variables using shifted names [1].
  In short, free variables are named and indexed, while bound variables use de Bruijn levels.

  This improves upon the locally nameless representation [2], where names are not indexed,
  and so need to be fresh in various contexts and substitutions.

  de Bruijn levels count from the out in: the outermost binding is 0.
  Scope safety [3], where the de Bruijn level never exceeds the current binding depth,
  is encoded in the type of the bound variable.

  Nameless representation contrasts with the conventional locally-named representation
  usually used in the surface syntax, where all variables have (unindexed) names.
  This representation, while more human-readable, allows variable shadowing
  and presents difficulties in checking alpha-equivalence.

  References:
  [1] Syntax with Shifted Names: https://icfp19.sigplan.org/details/tyde-2019-papers/11/Syntax-with-Shifted-Names
    * Reference implementation: https://github.com/lpw25/shifted-names
  [2] The Locally Nameless Representation: http://www.chargueraud.org/research/2009/ln/main.pdf
  [3] Type and Scope Safe Syntaxes: https://arxiv.org/abs/2001.11001

  Variable convention:
  * i, j for Name indices
  * a, b for Names
  * l for de Bruijn levels
  * k, n, m for Var/Term type indices (binding depth)
  * x, y for Vars
  * t for the abstract Term type
  * e, u for Terms (the latter for substituted Terms)
  * a, b also for Terms that are types
-}

import Data.Fin

%default total

-- DEFINITIONS

Index : Type
Index = Nat

||| A Name is an identifier + an index;
||| shadowed names have different indices.
record Name where
  constructor mkName
  name : String
  index : Index

Eq Name where
  n1 == n2 = n1.name == n2.name && n1.index == n2.index

||| Locally-nameless representation of variables:
||| free variables are named, but
||| bound variables are represented using de Bruijn levels
||| (level 0 is the outermost, level (n-1) is the innermost).
||| We restrict levels to the range [0, n-1] using finite sets.
data Var : Nat -> Type where
  Bound : Fin k -> Var k
  Free : Name -> Var k

Eq (Var k) where
  Bound l1 == Bound l2 = l1 == l2
  Free a1 == Free a2 = a1 == a2
  _ == _ = False

-- Needed for push/pop (it should be in a Nat library somewhere...).
plus_comm_S : (n, m: Nat) -> n + S m = S (n + m)
plus_comm_S Z _ = Refl
plus_comm_S (S n) m = cong S $ plus_comm_S n m

interface Term (t : Nat -> Type) where
  pop : t (S (n + m)) -> t (n + S m)
  pop e = rewrite plus_comm_S n m in e

  push : t (n + S m) -> t (S (n + m))
  push e = rewrite sym $ plus_comm_S n m in e

  unit : Var k -> t k
  kmap : ({k: Nat} -> Var (n + k) -> t (m + k)) -> ({k: Nat} -> t (n + k) -> t (m + k))


-- HELPERS

||| shift_index i j = if i <= j then j + 1 else j
||| @ i the new open index
||| @ j the shifted index
||| Increment name index only if the current index is <= the one being opened.
shift_index : Index -> Index -> Index
shift_index Z j = (S j)
shift_index i Z = Z
shift_index (S i) (S j) = S (shift_index i j)

||| unshift_index i j = if i == j then None else if i < j then j - 1 else j
||| @ i the close index
||| @ j the shifted index
||| Decrement index only if the current index is <= the one being opened,
||| and > 0, and not the same as the one being closed.
||| Because the free variable being closed would have become a bound variable,
||| we never need to shift a name with the same index.
||| Also, shift will never open to a name with index Z, so we would never close it.
unshift_index : Index -> Index -> Maybe Index
unshift_index Z Z = Nothing
unshift_index Z (S j) = Just j
unshift_index _ Z = Just Z
unshift_index (S i) (S j) = S <$> unshift_index i j

||| @ a the name being opened
||| @ b the name being shifted
||| Shift b's index only if a and b's names collide.
shift_name : Name -> Name -> Name
shift_name a b =
  if a.name == b.name
  then mkName b.name (shift_index a.index b.index)
  else b

||| @ a the name being closed
||| @ b the name being shifted
||| Unshift b's index only if a and b's names collide
unshift_name : Name -> Name -> Maybe Name
unshift_name a b =
  if a.name == b.name
  then mkName b.name <$> (unshift_index a.index b.index)
  else Just b


-- PRIMITIVE VAR OPERATIONS

open_var : Name -> Var (S k) -> Var k
open_var name (Bound FZ) = Free name
open_var name (Bound (FS l)) = Bound l
open_var name (Free a) = Free $ shift_name name a

close_var : Name -> Var k -> Var (S k)
close_var bound (Bound l) = Bound (FS l)
close_var name (Free a) = maybe (Bound FZ) Free $ unshift_name name a

wk_var : Var k -> Var (S k)
wk_var (Bound l) = Bound (FS l)
wk_var (Free a) = Free a

bind_var : Var (S k) -> Maybe (Var k)
bind_var (Bound FZ) = Nothing
bind_var (Bound (FS l)) = Just $ Bound l
bind_var (Free a) = Just $ Free a


-- PRIMITIVE TERM OPERATIONS

open_term : Term t => {k: Nat} -> Name -> t (S k) -> t k
open_term name = kmap {n = S Z} {m = Z} (unit . open_var name)

close_term : Term t => {k: Nat} -> Name -> t k -> t (S k)
close_term name = kmap {n = Z} {m = S Z} (unit . close_var name)

wk_term : Term t => {k: Nat} -> t k -> t (S k)
wk_term = kmap {n = Z} {m = S Z} (unit . wk_var)

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

wkk_term : Term t => {k: Nat} -> t Z -> t k
wkk_term {k = Z} e = e
wkk_term {k = S k'} e = wk_term (wkk_term {k = k'} e)

bind_term : Term t => {k: Nat} -> t Z -> t (S k) -> t k
bind_term u = kmap {n = S Z} {m = Z} bind
where
  bind : {k: Nat} -> Var (S k) -> t k
  bind = (maybe (wkk_term u) unit . bind_var)


-- DERIVED TERM OPERATIONS

||| @ old the name to be replaced
||| @ new the name to replace with
||| Rename `old` to `new` by turning `old` into
||| a bound variable then opening it as `new`.
rename : Term t => {k: Nat} -> Name -> Name -> t k -> t k
rename old new = open_term new . close_term old

||| @ name the name to be replaced
||| @ u the term to replace with
||| Substitute in a capture-avoiding manner
||| (since `wkk` will shift `u` up as needed).
subst : Term t => {k: Nat} -> Name -> t Z -> t k -> t k
subst name u = bind_term u . close_term name

||| @ name the fresh name
||| Ensure that `name` is fresh by
||| creating a new binding and opening it as `name`.
shift : Term t => {k: Nat} -> Name -> t k -> t k
shift name = open_term name . wk_term


-- CONTEXTS

data Context : Type -> Type where
  Empty : Context t
  Cons : Context t -> Name -> t -> Context t

has : Context t -> Var Z -> t -> Type
has Empty _ _ = Void
has (Cons ctx y b) x a =
  case bind_var (close_var y x) of
    Nothing => b = a
    Just x' => has ctx x' a


-- PROPERTIES and LEMMAS

-- Lemma: Unshifting equal indices gets you nothing.
unshift_equal : (i: Index) -> unshift_index i i = Nothing
unshift_equal Z = Refl
unshift_equal (S i) = rewrite unshift_equal i in Refl

-- Theorem: Unshifting a shifted index should do nothing.
unshift_shift_index : (i, j: Index) -> unshift_index i (shift_index i j) = Just j
unshift_shift_index Z _ = Refl
unshift_shift_index (S i) Z = Refl
unshift_shift_index (S i) (S j) = rewrite unshift_shift_index i j in Refl

indistinct_names : (a, b: Name) -> Type
indistinct_names a b = a.name == b.name = True

distinct_names : (a, b: Name) -> Type
distinct_names a b = a.name == b.name = False

indistinct_indices : (a, b: Name) -> Type
indistinct_indices a b = a.index == b.index = True

distinct_indices : (a, b: Name) -> Type
distinct_indices a b = a.index == b.index = False

-- Lemma: Indistinct names are equal.
indistinct_names_eq : (a, b: Name) -> indistinct_names a b -> a.name = b.name
indistinct_names_eq a b indistinct = ?todo_indnaeq

-- Lemma: Indistinct indices are equal.
indistinct_indices_eq : (a, b: Name) -> indistinct_indices a b -> a.index = b.index
indistinct_indices_eq a b indistinct = ?todo_indindeq

-- Lemma: A name is made up of its parts.
name_eta : (a: Name) -> mkName a.name a.index = a
name_eta (mkName name index) = Refl

-- Lemma: Shifting something with a different name should do nothing.
shift_distinct_name : {a, b: Name} -> distinct_names a b -> shift_name a b = b
shift_distinct_name distinct = rewrite distinct in Refl

-- Lemma: Shifting something with the same name shifts the index.
shift_indistinct_name : {a, b: Name} -> indistinct_names a b -> shift_name a b = mkName b.name (shift_index a.index b.index)
shift_indistinct_name indistinct = rewrite indistinct in Refl

-- Lemma: Unshifting something with a different name should do nothing.
unshift_distinct_name : {a, b: Name} -> distinct_names a b -> unshift_name a b = Just b
unshift_distinct_name distinct = rewrite distinct in Refl

-- Lemma: Unshifting something with the same name shifts the index unless they are the same.
unshift_indistinct_name : {a, b: Name} -> indistinct_names a b -> unshift_name a b = mkName b.name <$> (unshift_index a.index b.index)
unshift_indistinct_name indistinct = rewrite indistinct in Refl

-- Lemma: Two names are either distinct or indistinct.
distinct_indistinct_name : (a, b: Name) -> Either (distinct_names a b) (indistinct_names a b)
distinct_indistinct_name a b = ?todo_di_name

-- Lemma: Two indices are either distinct or indistinct.
distinct_indistinct_index : (a, b: Name) -> Either (distinct_indices a b) (indistinct_indices a b)
distinct_indistinct_index a b = ?todo_di_index

-- Theorem: Unshifting a shifted name should do nothing.
unshift_shift_name : (a, b: Name) -> unshift_name a (shift_name a b) = Just b
unshift_shift_name a b =
  case distinct_indistinct_name a b of
    Left  l => rewrite l in rewrite l in Refl
    Right r =>
      rewrite r in rewrite r in
      rewrite unshift_shift_index (index a) (index b) in
      rewrite name_eta b in Refl

-- Theorem: Shifting an unshifted name should do nothing.
shift_unshift_name : (a, b: Name) -> shift_name a <$> unshift_name a b = if a == b then Nothing else Just b
shift_unshift_name a b =
  case distinct_indistinct_name a b of
    Left  ln => rewrite ln in rewrite ln in Refl
    Right rn =>
      rewrite rn in
      case distinct_indistinct_index a b of
        Left  li => rewrite li in ?todo_su_rnli
        Right ri =>
          rewrite ri in
          rewrite sym $ indistinct_indices_eq a b ri in
          rewrite unshift_equal (index a) in Refl

-- Theorem: Opening and closing a name in variables are inverses.
open_close_var : {a: Name} -> {x: Var k} -> open_var a (close_var a x) = x
close_open_var : {a: Name} -> {x: Var (S k)} -> close_var a (open_var a x) = x

-- Theorem: bind_var . wk_var should do nothing.
bind_wk_var : {x: Var k} -> bind_var (wk_var x) = Just x
bind_wk_var {x = Bound l} = Refl
bind_wk_var {x = Free a} = Refl

-- Theorem: Opening and closing a name are inverses.
open_close : Term t => {a: Name} -> {e: t k} -> open_term a (close_term a e) = e
close_open : Term t => {a: Name} -> {e: t (S k)} -> close_term a (open_term a e) = e

-- Theorem: Binding to a new unused bound variable should do nothing.
bind_wk : Term t => {u, e: t Z} -> bind_term u (wk_term e) = e

-- Theorem: Renaming a variable by itself should do nothing.
rename_refl : Term t => {a: Name} -> {e: t k} -> rename a a e = e

-- Theorem: Renaming should be transitive.
rename_trans : Term t => {a, b, c: Name} -> {e: t k} -> rename b c (rename a b e) = rename a c e

-- Theorem: Renaming a variable and then renaming it back should do nothing.
rename_symm : Term t => {a, b: Name} -> {e: t k} -> rename b a (rename a b e) = e

-- Theorem: Renaming then substituting should be the same as substituting the original variable.
subst_rename : Term t => {a, b: Name} -> {u: t Z} -> {e : t k} -> subst b (rename a b u) e = subst a u e

-- Theorem: Substituting an unused variable should do nothing.
subst_shift : Term t => {a: Name} -> {u: t Z} -> {e : t k} -> subst a (shift a u) e = e

-- Theorem: Summoning free variable b after renaming from a is the same as summoning free variable a.
shift_rename : Term t => {a, b: Name} -> {e: t k} -> shift b (rename a b e) = shift a e
