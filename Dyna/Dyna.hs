module Dyna where

import Control.Comonad

data Fix f = In {
  out :: f (Fix f)
}

data Cofree f a = Node {
  root :: a,
  subs :: f (Cofree f a)
}

instance Functor f => Functor (Cofree f) where
  fmap f (Node root subs) = Node (f root) (fmap (fmap f) subs)

instance Functor f => Comonad (Cofree f) where
  extract = root
  extend f x = Node (f x) (fmap (extend f) (subs x))

data Free f a = Pure a | Bind (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Bind x) = Bind (fmap (fmap f) x)

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure f <*> x = fmap f x
  Bind f <*> x = Bind (fmap (\f -> f <*> x) f)

instance Functor f => Monad (Free f) where
  Pure x >>= f = f x
  Bind m >>= f = Bind (fmap (>>= f) m)

cata :: Functor f => (f a -> a) -> Fix f -> a
cata phi = phi . fmap (cata phi) . out

ana :: Functor f => (a -> f a) -> a -> Fix f
ana psi = In . fmap (ana psi) . psi

histo :: Functor f => (f (Cofree f a) -> a) -> Fix f -> a
histo phi = root . cata (\x -> Node (phi x) x)

futu :: Functor f => (a -> f (Free f a)) -> a -> Fix f
futu psi = ana (fmap f) . psi where
  f (Pure x) = psi x
  f (Bind x) = x

dyna :: Functor f => (f (Cofree f b) -> b) -> (a -> f a) -> a -> b
dyna phi psi = histo phi . ana psi

data NatF x = Zero | Succ x
type Nat = Fix NatF

instance Functor NatF where
  fmap f Zero = Zero
  fmap f (Succ x) = Succ (f x)

zero :: Nat
zero = In Zero

succ :: Nat -> Nat
succ = In . Succ

toNum :: Num a => Nat -> a
toNum (In Zero) = 0
toNum (In (Succ x)) = 1 + toNum x

fromInt :: (Ord a, Integral a) => a -> Nat
fromInt n
  | n == 0 = In Zero
  | n  > 0 = In (Succ (fromInt (n - 1)))
  | otherwise = undefined

instance Show Nat where
  show = show . toNum

fib :: Nat -> Nat
fib = histo phi where
  phi :: NatF (Cofree NatF Nat) -> Nat
  phi Zero = fromInt 1
  phi (Succ (Node _ Zero)) = fromInt 1
  phi (Succ (Node fib' (Succ (Node fib'' _)))) =
    fromInt $ toNum fib' + toNum fib''

{-
fib 3
= histo phi 3
= root . cata (\x -> Node (phi x) x) $ 2
= root . (\x -> Node (phi x) x) . fmap (cata (\x -> Node (phi x) x)) $ 2
= root . (\x -> Node (phi x) x) $ 1 + cata (\x -> Node (phi x) x) 2
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) . fmap (cata (\x -> Node (phi x) x)) $ 2
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $ 1 + cata (\x -> Node (phi x) x) 1
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + cata (\x -> Node (phi x) x) 0
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) 0
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + Node 1 0
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + Node 1 (1 + Node 1 0)
= root . (\x -> Node (phi x) x) $
  1 + Node (1 + 1) (1 + Node 1 (1 + Node 1 0))
= root . Node 3 (1 + Node 2 (1 + Node 1 (1 + Node 1 0)))
-}

{-
fib 3
= histo phi 3
= root . (\x -> Node (phi x) x) $
  1 + cata (\x -> Node (phi x) x) 2
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + cata (\x -> Node (phi x) x) 1
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + cata (\x -> Node (phi x) x) 0
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) 0
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + Node 1 0
= root . (\x -> Node (phi x) x) $
  1 + (\x -> Node (phi x) x) $
  1 + Node 1 (1 + Node 1 0)
= root . (\x -> Node (phi x) x) $
  1 + Node (1 + 1) (1 + Node 1 (1 + Node 1 0))
= root . Node 3 (1 + Node 2 (1 + Node 1 (1 + Node 1 0)))
= 3
-}

main :: IO ()
main = pure ()