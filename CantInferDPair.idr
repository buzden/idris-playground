data A : Nat -> Type
data B : Nat -> Type
data C : Type

ab : A n -> B n
bc : B n -> C

f : Monad m => m (n ** A n) -> m C
f x = ({-the (m $ DPair ? $ \_ => ?) $-} map (\(n ** a) => (n ** ab a)) x) >>= \(n ** b) => pure $ bc b
