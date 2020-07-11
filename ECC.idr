main : IO ()
main = putStrLn "ECC"

data Zero : Type where
  Empty : Zero

data Succ : Type -> Type where
  LZ : Succ s
  LS : s -> Succ s

level : Nat -> Type
level Z = Zero
level (S n) = Succ (level n)

record Name where
  constructor mkName
  name : String
  index : Nat

data Var : Nat -> Type where
  Free : Name -> Var n
  Bound : (level n) -> Var n

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