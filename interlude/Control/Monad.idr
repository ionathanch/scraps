module Control.Monad

infixl 1 >>
infixr 1 =<<
infixr 1 >=>
infixr 1 <=<

%inline
export
(>>) : Monad m => m a -> m b -> m b
m >> k = m >>= \_ => k

export
(=<<) : Monad m => (a -> m b) -> m a -> m b
f =<< x = x >>= f

export
(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g

export
(<=<) : Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

%allow_overloads (>>)
%allow_overloads (=<<)
%allow_overloads (>=>)
%allow_overloads (<=<)
