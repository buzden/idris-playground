0 Pierce : Type -> Type
Pierce p = forall q. ((p -> q) -> p) -> p

P_to_EM : Pierce p -> (Not (Not p) -> p)
P_to_EM f g = f $ absurd . g
