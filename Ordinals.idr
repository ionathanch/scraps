{-
  A construction of the first few large ordinals,
  following "Ordinals in Type Theory":
  http://www.cse.chalmers.se/~coquand/ord.html
  http://www.cse.chalmers.se/~coquand/ordinal.ps
-}

data Ord: Type where
  O: Ord
  S: Ord -> Ord
  L: (Nat -> Ord) -> Ord

-- f o n is the ordinal o+n
f: Nat -> Ord -> Ord
f Z o = o
f (S n) o = S (f n o)

-- h Z is the ordinal O
-- h (S Z) is the limit of O+1, O+2, ... = ω
-- h (S (S Z)) is the limit of ω+1, ω+2, ... = 2ω
-- h n is the ordinal nω
h: Nat -> Ord
h Z = O
h (S n) = L (\k => f k (h n))

-- The limit ordinal ω² by taking the limit of O, ω, 2ω, ...
omega2: Ord
omega2 = L h


{- Sand reckoner with Gentzen's trick (???) -}

record LimitStructure X where
  constructor mkLS
  a: X
  f: X -> X
  l: (Nat -> X) -> X

iterate: (x -> x) -> Nat -> (x -> x)
iterate f Z x = f x
iterate f (S n) x = f (iterate f n x)

omega: (ls: LimitStructure x) -> x
omega (mkLS a f l) = l (\n => iterate f n a)

X: Type
X = Ord -> Ord

A: LimitStructure X
A = (mkLS id (S .) (\u, x => L (\n => u n x)))

h': (ls: LimitStructure X) -> X -> X
h' ls x = ls.l (iterate x)

up: LimitStructure X -> LimitStructure X
up a = mkLS S (h' a) (a.l)

-- ω^ω
omegaomega: Ord -> Ord
omegaomega = omega (up A)

-- The Hardy hierarchy
H: LimitStructure (Nat -> Nat)
H = (mkLS (+ 1) (\h, n => h (n + 1)) (\f, n => f n n))
