||| A sum type, isomorphic to Result,
||| but with a different name to make explicit
||| which constructor is for errors and which for successes.

module Data.Result

import Data.Option

%default total

public export
data Result : Type -> Type -> Type where
  Error : (1 _ : a) -> Result a b
  Ok    : (1 _ : b) -> Result a b

public export
toEither : Result a b -> Either a b
toEither (Error x) = Left x
toEither (Ok x)    = Right x

public export
fromEither : Either a b -> Result a b
fromEither (Left x)  = Error x
fromEither (Right x) = Ok x

public export
resultIsEither : {x: Either a b} -> toEither (fromEither x) = x
resultIsEither {x = Left l}  = Refl
resultIsEither {x = Right r} = Refl

public export
eitherIsResult : {x: Result a b} -> fromEither (toEither x) = x
eitherIsResult {x = Error e} = Refl
eitherIsResult {x = Ok k}    = Refl

-------------
-- PRELUDE --
-------------

||| Simply-typed eliminator for Result.
public export
result : Lazy (a -> c) -> Lazy (b -> c) -> Result a b -> c
result f g (Error x) = f x
result f g (Ok x)    = g x

public export
(Eq a, Eq b) => Eq (Result a b) where
  Error x == Error x' = x == x'
  Ok x    == Ok x'    = x == x'
  _ == _ = False

public export
(Ord a, Ord b) => Ord (Result a b) where
  compare (Error x) (Error x') = compare x x'
  compare (Error _) (Ok _)     = LT
  compare (Ok _)    (Error _)  = GT
  compare (Ok x)    (Ok x')    = compare x x'

%inline
public export
Functor (Result e) where
  map f (Error x) = Error x
  map f (Ok x)    = Ok (f x)

%inline
public export
Applicative (Result e) where
    pure = Ok

    (Error x) <*> _         = Error x
    (Ok f)    <*> (Ok x)    = Ok (f x)
    (Ok _)    <*> (Error x) = Error x

public export
Monad (Result e) where
    (Error x) >>= _ = Error x
    (Ok x) >>= f = f x

export
(Show a, Show b) => Show (Result a b) where
  showPrec d (Error x) = showCon d "Error" $ showArg x
  showPrec d (Ok x)    = showCon d "Ok"    $ showArg x

----------
-- BASE --
----------

||| True if the argument is Error, False otherwise
public export
isError : Result a b -> Bool
isError (Error _) = True
isError (Ok _)    = False

||| True if the argument is Ok, False otherwise
public export
isOk : Result a b -> Bool
isOk (Error _) = False
isOk (Ok _)    = True

||| Keep the payloads of all Error constructors in a list of Results
public export
errors : List (Result a b) -> List a
errors []              = []
errors (Error e :: xs) = e :: errors xs
errors (Ok _ :: xs)    = errors xs

||| Keep the payloads of all Ok constructors in a list of Results
public export
oks : List (Result a b) -> List b
oks []              = []
oks (Error _ :: xs) = oks xs
oks (Ok k :: xs)    = k :: oks xs

||| Split a list of Results into a list of the left elements and a list of the right elements
public export
partitionResults : List (Result a b) -> (List a, List b)
partitionResults l = (errors l, oks l)

||| Remove a "useless" Result by collapsing the case distinction
public export
fromResult : Result a a -> a
fromResult (Error l) = l
fromResult (Ok r) = r

||| Ok becomes Error and Error becomes Ok
public export
mirror : Result a b -> Result b a
mirror (Error x) = Ok x
mirror (Ok x)    = Error x

public export
optionToEither : (def : Lazy e) -> Option a -> Result e a
optionToEither def (Some j) = Ok j
optionToEither def None     = Error def

||| Convert a Result to an Option from Ok injection
public export
resultToOption : Result e a -> Option a
resultToOption (Error _) = None
resultToOption (Ok x)    = Some x

-- Injectivity of constructors

||| Error is injective
errorInjective : Error x = Error y -> x = y
errorInjective Refl = Refl

||| Ok is injective
okInjective : Ok x = Ok y -> x = y
okInjective Refl = Refl

-------------
-- HASKELL --
-------------

public export
Semigroup (Result a b) where
  Error _ <+> b = b
  a       <+> _ = a

public export
Foldable (Result a) where
  foldr _ z (Error _) = z
  foldr f z (Ok x) = f x z

public export
Traversable (Result a) where
  traverse _ (Error x) = pure (Error x)
  traverse f (Ok y)    = Ok <$> (f y)

public export
fromError : a -> Result a b -> a
fromError _ (Error a) = a
fromError a _         = a

public export
fromOk : b -> Result a b -> b
fromOk _ (Ok a) = a
fromOk a _      = a
