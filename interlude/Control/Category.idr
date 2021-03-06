module Control.Category

import Data.Morphisms

infixr 9 .
infixr 1 <<<
infixr 1 >>>

public export
interface Category (cat : Type -> Type -> Type) where
  id    : cat a a
  (.)   : cat b c -> cat a b -> cat a c
  (<<<) : cat b c -> cat a b -> cat a c
  (>>>) : cat a b -> cat b c -> cat a c
  (<<<) = (.)
  (>>>) = flip (.)

interface Category cat => CategoryV (cat : Type -> Type -> Type) where
  categoryRightIdentity : {f : cat a b} -> f . id {cat = cat} = f
  categoryLeftIdentity  : {f : cat a b} -> id {cat = cat} . f = f
  categoryAssociativity : {f : cat c d} -> {g  : cat b c} -> {h : cat a b} -> f . (g . h) = (f . g) . h

export
Category Morphism where
  id = Mor Prelude.id
  (Mor f) . (Mor g) = Mor (f . g)

export
Monad f => Category (Kleislimorphism f) where
  id = Kleisli pure
  (Kleisli f) . (Kleisli g) = Kleisli (\r => g r >>= f)
