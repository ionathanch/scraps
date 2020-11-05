module Data.Ord

export
comparing : Ord a => (b -> a) -> b -> b -> Ordering
comparing p x y = compare (p x) (p y)
