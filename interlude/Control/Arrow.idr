module Control.Arrow

import Data.Tuple
import Data.Either
import Data.Morphisms
import Control.Category

infixr 1 ~>
infixr 5 <+>
infixr 3 ***
infixr 3 &&&
infixr 2 +++
infixr 2 \|/
infixr 1 ^>>, >>^
infixr 1 ^<<, <<^

public export
interface Category a => Arrow a where
  arr : (b ~> c) -> a b c

  first : a b c -> a (b, d) (c, d)
  first f = f *** id

  second : a b c -> a (d, b) (d, c)
  second g = id *** g

  (***) : a b c -> a b' c' -> a (b, b') (c, c')
  f *** g = first f >>> second g

  (&&&) : a b c -> a b c' -> a b (c, c')
  f &&& g = arr (Mor {a = b} {b = (b, b)} \b => (b, b)) >>> f *** g

  (^>>) : (b ~> c) -> a c d -> a b d
  f ^>> a = arr f >>> a

  (>>^) : a c d -> (b ~> c) -> a b d
  a >>^ f = a <<< arr f

  (<<^) : a c d -> (b ~> c) -> a b d
  a <<^ f = a <<< arr f

  (^<<) : (c ~> d) -> a b c -> a b d
  f ^<< a = arr f <<< a

public export
interface Arrow a => ArrowV a where
  identity      : arr {a = a} id = Category.id
  composeArr    : {f : c ~> d} -> {g : b ~> c} -> (arr f)    . (arr g)    = arr {a = a} (f . g)
  composeFirst  : {f : a c d}  -> {g : a b c}  -> (first f)  . (first g)  = first (f . g)
  composeSecond : {f : a c d}  -> {g : a b c}  -> (second f) . (second g) = second (f . g)


public export
Arrow Morphism where
  arr = id
  (Mor f) *** (Mor g) = (Mor \(x, y) => (f x, g y))

public export
Monad m => Arrow (Kleislimorphism m) where
  arr (Mor f) = Kleisli (pure . f)
  (Kleisli f) *** (Kleisli g) =
    Kleisli (\(x, y) => do
      x' <- f x
      y' <- g y
      pure (x', y'))

-- Arrow laws for Morphism
firstArr : first {a = Morphism} (arr f) = arr (first f)
firstArr = Refl

secondArr : second {a = Morphism} (arr f) = arr (second f)
secondArr = Refl

productArr : arr {a = Morphism} f *** arr {a = Morphism} g = arr (f *** g)
productArr = Refl

fanoutArr : arr {a = Morphism} f &&& arr {a = Morphism} g = arr (f &&& g)
fanoutArr = Refl


interface Arrow a => ArrowZero a where
  zeroArrow : a b c

(Alternative m, Monad m) => ArrowZero (Kleislimorphism m) where
  zeroArrow = empty

interface ArrowZero a => ArrowPlus a where
  (<+>) : a b c -> a b c -> a b c

(Alternative m, Monad m) => ArrowPlus (Kleislimorphism m) where
  (Kleisli f) <+> (Kleisli g) = Kleisli (\x => f x <|> g x)


interface Arrow a => ArrowChoice a where
  (+++) : a b c -> a b' c' -> a (Either b b') (Either c c')
  f +++ g = left f >>> right g

  left : a b c -> a (Either b d) (Either c d)
  left f = f +++ id

  right : a b c -> a (Either d b) (Either d c)
  right g = id +++ g

  (\|/) : a b d -> a c d -> a (Either b c) d
  f \|/ g = f +++ g >>> arr (Mor fromEither)

interface ArrowChoice a => ArrowChoiceV a where
  composeLeft  : {f : a c d} -> {g : a b c} -> left  f . left  g = left  {a = a} (f . g)
  composeRight : {f : a c d} -> {g : a b c} -> right f . right g = right {a = a} (f . g)


ArrowChoice Morphism where
  (Mor f) +++ (Mor g) = Mor (Left . f) \|/ Mor (Right . g)

Monad m => ArrowChoice (Kleislimorphism m) where
  (Kleisli f) +++ (Kleisli g) =
    Kleisli (\x =>
      case x of
        Left  l => Left  <$> f l
        Right r => Right <$> g r)

-- ArrowChoice laws for Morphism
leftArr  : left  {a = Morphism} (arr f) = arr (left f)
leftArr = Refl

rightArr : right {a = Morphism} (arr f) = arr (right f)
rightArr = Refl

sumArr   : arr {a = Morphism} f +++ arr {a = Morphism} g = arr (f +++ g)
sumArr = Refl

faninArr : arr {a = Morphism} f \|/ arr {a = Morphism} g = arr (f \|/ g)
faninArr = Refl


interface Arrow a => ArrowApply a where
  app : a (a b c, b) c

ArrowApply Morphism where
  app = Mor (\((Mor f), x) => f x)

Monad m => ArrowApply (Kleislimorphism m) where
  app = Kleisli (\(Kleisli f, x) => f x)


interface Arrow a => ArrowLoop a where
  loop : a (b, d) (c, d) -> a b c

{- I can't implement this. Where does `d` come from???
ArrowLoop Fun where
  loop (Lam f) = Lam (\b => let (c, d) = f (b, d) in c)
-}
