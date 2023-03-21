ana : (Not $ Not $ Not a) -> Not $ a
ana f x = f $ \y => y x

nana : (Not $ Not $ Not $ Not a) -> Not $ Not $ a
nana x y = x $ \z => z y

----

de_morgan : Not (Either a b) -> (Not a, Not b)
de_morgan f = (f . Left, f . Right)

constr_pem : Not $ Not $ Either a (Not a)
constr_pem = (\(x, y) => y x) . de_morgan

----

pem_to_dne : Either a (Not a) -> Not (Not a) -> a
pem_to_dne (Left x)  f = x
pem_to_dne (Right x) f = absurd $ f x

constr_dne : Not $ Not $ Not (Not a) -> a
constr_dne = constr_pem {a} . \x, y => x $ \z => pem_to_dne y z

----

not_implication : Not (a -> b) -> Not b
not_implication f x = f $ const x

dne_to_pem' : Not $ Not $ (Not (Not a) -> a) -> Either a (Not a)
dne_to_pem' = constr_pem . not_implication

dne_to_pem : (forall a. Not (Not a) -> a) -> Either a (Not a)
dne_to_pem f = f constr_pem
