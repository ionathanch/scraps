import Shifted

%default total

-- ECC (Extended Calculus of Constructions)
-- With definitions and dependent conditionals

data Expr : Nat -> Type where
  Id      : Var k -> Expr k                       -- Variables (shifted names)
  Prop    : Expr k                                -- Prop (impredicative)
  Typ     : Nat -> Expr k                         -- Type_i
  Pi      : Expr k -> Expr (S k) -> Expr k        -- Dependent function types: Π(x:A).B
  Abs     : Expr k -> Expr (S k) -> Expr k        -- Functions: λ(x:A).B
  App     : Expr k -> Expr k -> Expr k            -- Applications: e e
  Sigma   : Expr k -> Expr (S k) -> Expr k        -- Dependent pair types: Σ(x:A).B
  Pair    : Expr k -> Expr k -> Expr k -> Expr k  -- Pairs: ⟨e, e⟩ as T
  Fst     : Expr k -> Expr k                      -- First projection: π₁ e
  Snd     : Expr k -> Expr k                      -- Second projection: π₂ e
  Boolean : Expr k                                -- Boolean type
  True    : Expr k                                -- Boolean true
  False   : Expr k                                -- Boolean false
  If      : Expr k -> Expr k -> Expr k -> Expr k  -- Dependent conditionals: if e then e else e
  Let     : Expr k -> Expr (S k) -> Expr k        -- Definitions: let x = e in e

Term Expr where
  unit = Id
  kmap f (Id var)        = f var
  kmap _ Prop            = Prop
  kmap _ (Typ i)         = Typ i
  kmap f (Pi a b)        = Pi    (kmap f a)  (push (kmap f (assert_smaller b (pop b))))
  kmap f (Abs a e)       = Abs   (kmap f a)  (push (kmap f (assert_smaller e (pop e))))
  kmap f (App e1 e2)     = App   (kmap f e1) (kmap f e2)
  kmap f (Sigma a b)     = Sigma (kmap f a)  (push (kmap f (assert_smaller b (pop b))))
  kmap f (Pair e1 e2 a)  = Pair  (kmap f e1) (kmap f e2) (kmap f a)
  kmap f (Fst e)         = Fst   (kmap f e)
  kmap f (Snd e)         = Snd   (kmap f e)
  kmap _ Boolean         = Boolean
  kmap _ True            = True
  kmap _ False           = False
  kmap f (If e1 e2 e3)   = If    (kmap f e1) (kmap f e2) (kmap f e3)
  kmap f (Let e1 e2)     = Let   (kmap f e1) (push (kmap f (assert_smaller e2 (pop e2))))
