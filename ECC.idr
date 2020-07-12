import Shifted

%default total

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

map_var : (forall k. Var (k + n) -> Exp (k + m)) -> (forall k. Exp (k + n) -> Exp (k + m))
map_var f (Id var)        = f var
map_var _ Prop            = Prop
map_var _ (Typ i)         = Typ i
map_var f (Pi a b)        = Pi (map_var f a) (map_var f {k = S k} b)
map_var f (Abs a e)       = Abs (map_var f a) (map_var f {k = S k} e)
map_var f (App e1 e2)     = App (map_var f e1) (map_var f e2)
map_var f (Sigma a b)     = Sigma (map_var f a) (map_var f {k = S k} b)
map_var f (Pair e1 e2 a)  = Pair (map_var f e1) (map_var f e2) (map_var f a)
map_var f (Fst e)         = Fst (map_var f e)
map_var f (Snd e)         = Snd (map_var f e)
map_var _ Boolean         = Boolean
map_var _ True            = True
map_var _ False           = False
map_var f (If e1 e2 e3)   = If (map_var f e1) (map_var f e2) (map_var f e3)
map_var f (Let e1 e2)     = Let (map_var f e1) (map_var f {k = S k} e2)
