module Interlude

{-
  A package of common and renamed utilities.
  From Idris' base package:
  * Data.Morphisms
  From Haskell's base package:
  * Data.Tuple
  * Data.Ord
  * Data.Function
  * Data.Functor
  * Control.Applicative
  * Control.Alternative
  * Control.Monad
  * Control.Category
  * Control.Arrow
  Renamed:
  * Data.Maybe => Data.Option
  * Data.Either => Data.Result
  Renamed files are divided into different sections:
  * PRELUDE: From Idris' Prelude
  * BASE: From Idris' Base
  * CONTRIB: From Idris' Contrib
  * HASKELL: From Haskell's Prelude
-}

import public Data.Option
import public Data.Result
import public Data.Tuple
import public Data.Ord
import public Data.Function
import public Data.Morphisms
import public Data.Functor
import public Control.Applicative
import public Control.Alternative
import public Control.Monad
import public Control.Category
import public Control.Arrow
