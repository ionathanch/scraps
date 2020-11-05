module Control.Applicative

infixl 4 <**>

export
(<**>) : Applicative f => f a -> f (a -> b) -> f b
(<**>) = flip (<*>)
%allow_overloads (<**>)

export
unless : Applicative f => Bool -> Lazy (f ()) -> f ()
unless = when . not
