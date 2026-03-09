%default total
%unbound_implicits off

data Fun : (Type -> Unit) -> Type where

app : Type -> Unit
app (Fun f) = f (Fun f)
app _ = ()

loop : Unit
loop = app (Fun app)