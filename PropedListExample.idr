import Data.DPair
import Data.List.Elem
import Data.List.Quantifiers

data IsEven : Nat -> Type where
  Z : IsEven Z
  S : IsEven k -> IsEven $ S $ S k

data IsPower2 : Nat -> Type where
  Base : IsPower2 1
  Next : IsPower2 k -> IsPower2 (k + k)

InterestingList : Type
InterestingList = List Nat `Subset` \xs => (All IsEven xs, (p1 ** p2 ** (Elem p1 xs, Elem p2 xs, IsPower2 p1, IsPower2 p2, Not $ p1 === p2)))

lxs : InterestingList
lxs = Element [2, 4] (%search, (2 ** 4 ** (%search, %search, Next Base, Next $ Next Base, \case Refl impossible)))
