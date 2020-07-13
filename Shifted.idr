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
-}

import Data.Fin

%default total

-- DEFINITIONS

Index : Type
Index = Nat

-- A Name is an identifier + an index;
-- shadowed names have different indices.
record Name where
  constructor mkName
  name : String
  index : Index

Eq Name where
  n1 == n2 = n1.name == n2.name && n1.index == n2.index

-- Locally-nameless representation of variables:
-- free variables are named, but
-- bound variables are represented using de Bruijn levels
-- (level 0 is the outermost, level (n-1) is the innermost).
-- We restrict levels to the range [0, n-1] using finite sets.
data Var : Nat -> Type where
  Bound : Fin k -> Var k
  Free : Name -> Var k

Eq (Var k) where
  Bound l1 == Bound l2 = l1 == l2
  Free n1 == Free n2 = n1 == n2
  _ == _ = False

-- HELPERS

-- shift_index i j = if i <= j then j + 1 else j
-- where i is the new open index, j is the shifted index
-- Increment name index only if the current index is <= the one being opened.
shift_index : Index -> Index -> Index
shift_index Z j = (S j)
shift_index i Z = Z
shift_index (S i) (S j) = S (shift_index i j)

-- unshift_index i j = if i == j then None else if i < j then j - 1 else j
-- where i is the close index, j is the shifted index
-- Decrement index only if the current index is <= the one being opened,
-- and > 0, and not the same as the one being closed.
-- Because the free variable being closed would have become a bound variable,
-- we never need to shift a name with the same index.
-- Also, shift will never open to a name with index Z, so we would never close it.
unshift_index : Index -> Index -> Maybe Index
unshift_index Z Z = Nothing
unshift_index Z (S j) = Just j
unshift_index _ Z = Just Z
unshift_index (S i) (S j) = S <$> unshift_index i j

-- shift_name a b shifts b's index only if a and b's names collide
shift_name : Name -> Name -> Name
shift_name a b =
  if a.name == b.name
  then mkName b.name (shift_index a.index b.index)
  else b

-- unshift_name a b unshift's b's index only if a and b's names collide
unshift_name : Name -> Name -> Maybe Name
unshift_name a b =
  if a.name == b.name
  then mkName b.name <$> (unshift_index a.index b.index)
  else Just b


-- PRIMITIVE OPERATIONS

open_var : Name -> Var (S k) -> Var k
open_var name (Bound FZ) = Free name
open_var name (Bound (FS fin)) = Bound fin
open_var name (Free free) = Free $ shift_name name free

close_var : Name -> Var k -> Var (S k)
close_var bound (Bound fin) = Bound (FS fin)
close_var name (Free free) = maybe (Bound FZ) Free $ unshift_name name free

wk_var : Var k -> Var (S k)
wk_var (Bound fin) = Bound (FS fin)
wk_var (Free free) = Free free

bind_var : Var (S k) -> Maybe (Var k)
bind_var (Bound FZ) = Nothing
bind_var (Bound (FS fin)) = Just $ Bound fin
bind_var (Free free) = Just $ Free free


-- PROPERTIES and LEMMAS

-- Theorem: Unshifting a shifted index should do nothing.
unshift_shift_index : (i, j: Index) -> unshift_index i (shift_index i j) = Just j
unshift_shift_index Z _ = Refl
unshift_shift_index (S i) Z = Refl
unshift_shift_index (S i) (S j) = rewrite unshift_shift_index i j in Refl

indistinct_names : (a, b: Name) -> Type
indistinct_names a b = a.name = b.name

distinct_names : (a, b: Name) -> Type
distinct_names a b = (a.name = b.name) -> Void

-- Lemma: Shifting something with a different name should do nothing.
shift_distinct_name : {a, b: Name} -> distinct_names a b -> shift_name a b = b

-- Lemma: Shifting something with the same name shifts the index.
shift_indistinct_name : {a, b: Name} -> indistinct_names a b -> shift_name a b = mkName b.name (shift_index a.index b.index)

-- Lemma: Unshifting something with a different name should do nothing.
unshift_distinct_name : {a, b: Name} -> distinct_names a b -> unshift_name a b = Just b

-- Lemma: Unshifting something with the same name shifts the index unless they are the same.
unshift_indistinct_name : {a, b: Name} -> indistinct_names a b -> unshift_name a b = mkName b.name <$> (unshift_index a.index b.index)

-- Theorem: Unshifting a shifted name should do nothing.
unshift_shift_name : {a, b: Name} -> unshift_name a (shift_name a b) = Just b

-- Theorem: Shifting an unshifted name should do nothing. TODO: Maybe this should use a = b instead of a == b?
shift_unshift_name : {a, b: Name} -> shift_name a <$> unshift_name a b = if a == b then Nothing else Just b 

-- Theorem: open and close are inverses.
open_close : {a: Name} -> {x: Var k} -> open_var a (close_var a x) = x
close_open : {a: Name} -> {x: Var (S k)} -> close_var a (open_var a x) = x

-- Theorem: bind . wk should do nothing.
bind_wk_var : {x: Var k} -> bind_var (wk_var x) = Just x
