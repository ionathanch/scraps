-- Why is Functor in Data and not in Control?
module Data.Functor

infixr 4 <$
infixl 4 $>
infixr 1 <&>

export
(<$) : Functor f => a -> f b -> f a
(<$) = map . const

export
($>) : Functor f => f a -> b -> f b
($>) = flip (<$)

export
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) = flip map

export
void : Functor f => f a -> f ()
void x = x $> ()

%allow_overloads (<$)
%allow_overloads ($>)
%allow_overloads (<&>)
%allow_overloads Data.Functor.void
