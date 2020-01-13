||| In this Kata you'll learn Bisimulation
module BisiProof

%default total
%access export

namespace Bisimulation

	--This is the definition of Bisimulation: the inductive parts should
	--equivalent, and the coinductive parts should bisimulate.
	--With Cubical Model we can prove that Bisimulation is an equivlance,
	--aka Coinductive Proof Principle.
	--However, you don't have Cubical Model in Idris :(

	infixr 10 :=:
	public export
	codata Bisimulation : (x : Stream a) -> (y : Stream a) -> Type where
		(:=:) : {x : Stream a} -> {y : Stream a} ->
						(head x = head y) ->
						(Bisimulation (tail x) (tail y)) ->
						(Bisimulation x y)

||| Example: consider an infinite list of ones
Ones : Stream Nat
Ones = 1 :: Ones

onesBisimulation : Bisimulation Ones Ones
onesBisimulation = Refl :=: onesBisimulation

public export
Odd : Stream a -> Stream a
Odd l = head (tail l) :: Odd (tail (tail l))

public export
Even : Stream a -> Stream a
Even l = head l :: Even (tail (tail l))

public export
Merge : Stream a -> Stream a -> Stream a
Merge a b = head a :: head b :: Merge (tail a) (tail b)

public export
MergeOddEvenIsBisimulation : (x : Stream a) -> Bisimulation (Merge (Even x) (Odd x)) x
MergeOddEvenIsBisimulation x = Refl :=: Refl :=: MergeOddEvenIsBisimulation (tail . tail $ x)
