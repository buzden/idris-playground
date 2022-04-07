x = [not, id]

y : List $ forall a. a -> a
y = [id, id]

z : List (forall a. a -> a) -> List (forall a. a -> a)
z = Prelude.(::) id
