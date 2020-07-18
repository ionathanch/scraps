module Control.Alternative

import Data.Option

export
some : Alternative f => f a -> f (List a)
some v = some_v
  where
    many_v : f (List a)
    some_v : f (List a)
    many_v = some_v <|> pure Prelude.Nil
    some_v = (::) <$> v <*> many_v

export
many : Alternative f => f a -> f (List a)
many v = many_v
  where
    many_v : f (List a)
    some_v : f (List a)
    many_v = some_v <|> pure Prelude.Nil
    some_v = (::) <$> v <*> many_v

export
perhaps : Alternative f => f a -> f (Maybe a)
perhaps v = Just <$> v <|> pure Nothing

export
optional : Alternative f => f a -> f (Option a)
optional v = Some <$> v <|> pure None
