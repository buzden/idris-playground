import Data.DPair
import Data.List.Quantifiers

%default total

namespace ThroughFunction

  pushIn' : All p xs -> List $ Exists p
  pushIn' []      = []
  pushIn' (p::ps) = Evidence _ p :: pushIn' ps

  All2 : (0 _ : {0 x : a} -> f x -> Type) -> All f xs -> Type
  All2 g = All (uncurry g) . pushIn'

namespace ThroughData

  data All2 : ({0 x : a} -> f x -> Type) -> All f xs -> Type where
    Nil  : {0 f : a -> Type} -> {0 g : ({0 x : a} -> f x -> Type)} -> All2 g []
    (::) : {0 f : a -> Type} -> {0 g : ({0 x : a} -> f x -> Type)} ->
           {0 fx : f _} -> {0 fxs : All f _} -> g fx -> All2 g fxs -> All2 g (fx::fxs)
