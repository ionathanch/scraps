module Control.Arrow

import Data.Tuple
import Data.Either
import Control.Category

infixr 5 <+>
infixr 3 ***
infixr 3 &&&
infixr 2 +++
infixr 2 \|/
infixr 1 ^>>, >>^
infixr 1 ^<<, <<^

public export
interface Category a => Arrow a where
  arr : (b -> c) -> a b c

  first : a b c -> a (b, d) (c, d)
  first f = f *** id

  second : a b c -> a (d, b) (d, c)
  second g = id *** g

  (***) : a b c -> a b' c' -> a (b, b') (c, c')
  f *** g = first f >>> second g

  (&&&) : a b c -> a b c' -> a b (c, c')
  f &&& g = arr (\b => (b, b)) >>> f *** g

  (^>>) : (b -> c) -> a c d -> a b d
  f ^>> a = arr f >>> a

  (>>^) : a c d -> (b -> c) -> a b d
  a >>^ f = a <<< arr f

  (<<^) : a c d -> (b -> c) -> a b d
  a <<^ f = a <<< arr f

  (^<<) : (c -> d) -> a b c -> a b d
  f ^<< a = arr f <<< a

public export
interface Arrow a => ArrowV a where
  identity      : arr {a = a} id = Category.id
  composeArr    : {f : c -> d} -> {g : b -> c} -> (arr f)    . (arr g)    = arr {a = a} (f . g)
  composeFirst  : {f : a c d}  -> {g : a b c}  -> (first f)  . (first g)  = first (f . g)
  composeSecond : {f : a c d}  -> {g : a b c}  -> (second f) . (second g) = second (f . g)


-- A wrapper around function types,
-- since we can't refer directly to (->)
public export
record Fun a b where
  constructor Lam
  lam : (a -> b)

public export
Category Fun where
  id = Lam (\x => x)
  (Lam f) . (Lam g) = (Lam (f . g))

public export
Arrow Fun where
  arr f = (Lam f)
  (Lam f) *** (Lam g) = (Lam \(x, y) => (f x, g y))

-- Arrow laws for Fun
firstArr : first {a = Fun} (arr f) = arr (lam (first (Lam f)))
firstArr = Refl

secondArr : second {a = Fun} (arr f) = arr (lam (second (Lam f)))
secondArr = Refl

productArr : arr {a = Fun} f *** arr {a = Fun} g = arr (lam ((Lam f) *** (Lam g)))
productArr = Refl

fanoutArr : arr {a = Fun} f &&& arr {a = Fun} g = arr (lam ((Lam f) &&& (Lam g)))
fanoutArr = Refl


public export
record Kleisli (m : Type -> Type) a b where
  constructor mkKleisli
  runKleisli : (a -> m b)

public export
Functor m => Functor (Kleisli m a) where
  map f (mkKleisli g) = mkKleisli (map f . g)

public export
Applicative m => Applicative (Kleisli m a) where
  pure = mkKleisli . const . pure
  (mkKleisli f) <*> (mkKleisli g) = mkKleisli (\x => f x <*> g x)

public export
Alternative m => Alternative (Kleisli m a) where
  empty = mkKleisli $ const empty
  mkKleisli f <|> mkKleisli g = mkKleisli (\x => f x <|> g x)

public export
Monad m => Monad (Kleisli m a) where
  mkKleisli f >>= k = mkKleisli (\x => f x >>= \a => runKleisli (k a) x)

public export
Monad m => Category (Kleisli m) where
  id = mkKleisli pure
  (mkKleisli f) . (mkKleisli g) = mkKleisli (\b => g b >>= f)

public export
Monad m => Arrow (Kleisli m) where
  arr f = mkKleisli (pure . f)
  (mkKleisli f) *** (mkKleisli g) =
    mkKleisli (\(x, y) => do
      x' <- f x
      y' <- g y
      pure (x', y'))


interface Arrow a => ArrowZero a where
  zeroArrow : a b c

(Alternative m, Monad m) => ArrowZero (Kleisli m) where
  zeroArrow = empty

interface ArrowZero a => ArrowPlus a where
  (<+>) : a b c -> a b c -> a b c

(Alternative m, Monad m) => ArrowPlus (Kleisli m) where
  (mkKleisli f) <+> (mkKleisli g) = mkKleisli (\x => f x <|> g x)


interface Arrow a => ArrowChoice a where
  (+++) : a b c -> a b' c' -> a (Either b b') (Either c c')
  f +++ g = left f >>> right g

  left : a b c -> a (Either b d) (Either c d)
  left f = f +++ id

  right : a b c -> a (Either d b) (Either d c)
  right g = id +++ g

  (\|/) : a b d -> a c d -> a (Either b c) d
  f \|/ g = f +++ g >>> arr fromEither

interface ArrowChoice a => ArrowChoiceV a where
  composeLeft  : {f : a c d} -> {g : a b c} -> left  f . left  g = left  {a = a} (f . g)
  composeRight : {f : a c d} -> {g : a b c} -> right f . right g = right {a = a} (f . g)

ArrowChoice Fun where
  (Lam f) +++ (Lam g) = Lam (Left . f) \|/ Lam (Right . g)

Monad m => ArrowChoice (Kleisli m) where
  (mkKleisli f) +++ (mkKleisli g) =
    mkKleisli (\x =>
      case x of
        Left  l => Left  <$> f l
        Right r => Right <$> g r)

-- ArrowChoice laws for Fun
leftArr  : left  {a = Fun} (arr f) = arr (lam (left  (Lam f)))
rightArr : right {a = Fun} (arr f) = arr (lam (right (Lam f)))
sumArr   : arr {a = Fun} f +++ arr {a = Fun} g = arr (lam ((Lam f) +++ (Lam g)))
faninArr : arr {a = Fun} f \|/ arr {a = Fun} g = arr (lam ((Lam f) \|/ (Lam g)))


interface Arrow a => ArrowApply a where
  app : a (a b c, b) c

ArrowApply Fun where
  app = Lam (\((Lam f), x) => f x)

Monad m => ArrowApply (Kleisli m) where
  app = mkKleisli (\(mkKleisli f, x) => f x)


interface Arrow a => ArrowLoop a where
  loop : a (b, d) (c, d) -> a b c

{- I can't implement this. Where does `d` come from???
ArrowLoop Fun where
  loop (Lam f) = Lam (\b => let (c, d) = f (b, d) in c)
-}
