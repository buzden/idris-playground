%default total

data Wrapped a = Wrap a

-------------------------------

prefix 0 @@

(@@) : Nat -> a -> Wrapped a
(@@) _ = Wrap

x : List $ Wrapped String
x = [ (@@ 1) "wow" ]

-------------------------------

infixr 0 @@@

(@@@) : Nat -> a -> Wrapped a
(@@@) = (@@)

y : List $ Wrapped String
y = [ 5 @@@ "foo"
    , 5 @@@ id $ "bar"
    ]

-------------------------------

infix 0 @@@@

(@@@@) : a -> Nat -> Wrapped a
(@@@@) = flip (@@)

strid : String -> String
strid = id

z : List $ Wrapped String
z = [ "foo" @@@@ 4
    , (strid $ "bar") @@@@ 5
    ]
