import Shifted

%default total

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
