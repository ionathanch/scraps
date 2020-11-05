||| An optional value, isomorphic to Maybe,
||| but with a more commonplace name.

module Data.Option

%default total

public export
data Option : Type -> Type where
  None : Option a
  Some : (1 _ : a) -> Option a

public export
toMaybe : Option a -> Maybe a
toMaybe None = Nothing
toMaybe (Some x) = Just x

public export
fromMaybe : Maybe a -> Option a
fromMaybe Nothing = None
fromMaybe (Just x) = Some x

public export
maybeIsOption : {x: Maybe a} -> toMaybe (fromMaybe x) = x
maybeIsOption {x = Nothing}  = Refl
maybeIsOption {x = (Just a)} = Refl

public export
optionIsMaybe : {x: Option a} -> fromMaybe (toMaybe x) = x
optionIsMaybe {x = None}     = Refl
optionIsMaybe {x = (Some a)} = Refl

-------------
-- PRELUDE --
-------------

public export
Uninhabited (None = Some x) where
  uninhabited Refl impossible
 
public export
Uninhabited (Some x = None) where
  uninhabited Refl impossible
 
public export
value : Lazy b -> Lazy (a -> b) -> Option a -> b
value n j None     = n
value n j (Some x) = j x
 
public export
Eq a => Eq (Option a) where
  None     == None     = True
  None     == (Some _) = False
  (Some _) == None     = False
  (Some a) == (Some b) = a == b
 
public export
Ord a => Ord (Option a) where
  compare None     None     = EQ
  compare None     (Some _) = LT
  compare (Some _) None     = GT
  compare (Some a) (Some b) = compare a b
 
public export
Semigroup (Option a) where
  None     <+> m = m
  (Some x) <+> _ = Some x
 
public export
Monoid (Option a) where
  neutral = None
 
public export
Functor Option where
  map f (Some x) = Some (f x)
  map f None     = None
 
public export
Applicative Option where
  pure = Some
  Some f <*> Some a = Some (f a)
  _      <*> _      = None
 
public export
Alternative Option where
  empty = None
  (Some x) <|> _ = Some x
  None     <|> v = v
 
public export
Monad Option where
  None     >>= k = None
  (Some x) >>= k = k x
 
public export
Foldable Option where
  foldr _ z None     = z
  foldr f z (Some x) = f x z
 
public export
Traversable Option where
  traverse f None     = pure None
  traverse f (Some x) = Some <$> (f x)

export
Show a => Show (Option a) where
  showPrec d None     = "None"
  showPrec d (Some x) = showCon d "Some" (showArg x)

----------
-- BASE --
----------

public export
isNone : Option a -> Bool
isNone None     = True
isNone (Some _) = False

public export
isSome : Option a -> Bool
isSome None     = False
isSome (Some _) = True

||| Proof that some `Option` is actually `Some`
public export
data IsSome : Option a -> Type where
  ItIsSome : IsSome (Some x)

export
Uninhabited (IsSome None) where
  uninhabited ItIsSome impossible

||| Decide whether a 'Option' is 'Some'
public export
isItSome : (v : Option a) -> Dec (IsSome v)
isItSome (Some _) = Yes ItIsSome
isItSome None     = No absurd

||| Convert a `Option a` value to an `a` value by providing a default `a` value
||| in the case that the `Option` value is `None`.
public export
fromOption : (Lazy a) -> Option a -> a
fromOption def None     = def
fromOption _   (Some j) = j

||| Returns the `a` value of a `Option a` which is proved `Some`.
public export
fromSome : (v : Option a) -> IsSome v => a
fromSome (Some x) = x
fromSome None impossible

||| Returns `Some` the given value if the conditional is `True`
||| and `None` if the conditional is `False`.
public export
toOption : Bool -> Lazy a -> Option a
toOption True  j = Some j
toOption False _ = None

export
justInjective : Some x = Some y -> x = y
justInjective Refl = Refl

||| Convert a `Option a` value to an `a` value, using `neutral` in the case
||| that the `Option` value is `None`.
public export
lowerOption : Monoid a => Option a -> a
lowerOption None = neutral
lowerOption (Some x) = x

||| Returns `None` when applied to `neutral`, and `Some` the value otherwise.
export
raiseToOption : (Monoid a, Eq a) => a -> Option a
raiseToOption x = if x == neutral then None else Some x

-------------
-- HASKELL --
-------------

-- These were originally list-based functions,
-- but we can generalize them to some interfaces.

export
optionToAlt : Alternative m => Option a -> m a
optionToAlt None = empty
optionToAlt (Some a) = pure a

export
catOptions : (Alternative m, Monad m) => m (Option a) -> m a
catOptions mopt = do
  opt <- mopt
  case opt of
    None => empty
    Some x => pure x

export
mapOptions : (Alternative m, Monad m) => (a -> Option b) -> m a -> m b
mapOptions f x = catOptions $ f <$> x
