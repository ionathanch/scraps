main : IO ()
main = putStrLn "ECC"

%default total

-- DEFINITIONS

data Zero : Type where
  Empty : Zero

data Succ : Type -> Type where
  LZ : Succ s
  LS : s -> Succ s

level : Nat -> Type
level Z = Zero
level (S n) = Succ (level n)

Index : Type
Index = Nat

record Name where
  constructor mkName
  name : String
  index : Index

Eq Name where
  a == b = a.name == b.name && a.index == b.index

data Var : Nat -> Type where
  Free : Name -> Var n
  Bound : (level n) -> Var n

-- NAME SHIFTING

-- shift_index i j = if i <= j then j + 1 else j
-- where i is the new open index, j is the shifted index
shift_index : Index -> Index -> Index
shift_index Z j = (S j)
shift_index i Z = Z
shift_index (S i) (S j) = S (shift_index i j)

-- unshift_index i j = if i == j then None else if i < j then j - 1 else j
-- where i is the close index, j is the shifted index
unshift_index : Index -> Index -> Maybe Index
unshift_index Z Z = Nothing
unshift_index Z (S j) = Just j
unshift_index _ Z = Just Z
unshift_index (S i) (S j) = S <$> unshift_index i j

-- Lemma: unshifting a shifted index should do nothing
unshift_shift_index : (i, j: Index) -> unshift_index i (shift_index i j) = Just j
unshift_shift_index Z _ = Refl
unshift_shift_index (S i) Z = Refl
unshift_shift_index (S i) (S j) = rewrite unshift_shift_index i j in Refl

-- shift_name a b shifts b's index only if a and b's names collide
shift_name : Name -> Name -> Name
shift_name a b =
  if a.name == b.name
  then mkName b.name (shift_index a.index b.index)
  else b

-- unshift_name a b unshift's b's index only if a and b's names collide but aren't the same name
unshift_name : Name -> Name -> Maybe Name
unshift_name a b =
  if a.name == b.name
  then mkName b.name <$> (unshift_index a.index b.index)
  else Just b

indistinct_names : (a, b: Name) -> Type
indistinct_names a b = a.name = b.name

distinct_names : (a, b: Name) -> Type
distinct_names a b = a.name = b.name -> Void

-- Lemma: shifting something with a distinct name should do nothing
shift_distinct_name : (a, b: Name) -> distinct_names a b -> shift_name a b = b

-- Lemma: unshifting a shifted name should do nothing
unshift_shift_name : (a, b: Name) -> unshift_name a (shift_name a b) = Just b

-- ECC

-- Nat index indicates binding depth
data Exp : Nat -> Type where
  Id      : Var n -> Exp n                    -- Variables (shifted names)
  Prop    : Exp n                             -- Prop (impredicative)
  Typ     : Nat -> Exp n                      -- Type_i
  Pi      : Exp n -> Exp (S n) -> Exp n       -- Dependent function types: Π(x:A).B
  Abs     : Exp n -> Exp (S n) -> Exp n       -- Functions: λ(x:A).B
  App     : Exp n -> Exp n -> Exp n           -- Applications: e e
  Sigma   : Exp n -> Exp (S n) -> Exp n       -- Dependent pair types: Σ(x:A).B
  Pair    : Exp n -> Exp n -> Exp n -> Exp n  -- Pairs: ⟨e, e⟩ as T
  Fst     : Exp n -> Exp n                    -- First projection: π₁ e
  Snd     : Exp n -> Exp n                    -- Second projection: π₂ e
  Boolean : Exp n                             -- Boolean type
  True    : Exp n                             -- Boolean true
  False   : Exp n                             -- Boolean false
  If      : Exp n -> Exp n -> Exp n -> Exp n  -- Dependent conditionals: if e then e else e
  Let     : Exp n -> Exp (S n) -> Exp n       -- Definitions: let x = e in e
