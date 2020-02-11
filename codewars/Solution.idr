module Solution

namespace Preloaded

  %access export
  %default total

  ltePlus : LTE m1 n1 -> LTE m2 n2 -> LTE (m1 + m2) (n1 + n2)
  ltePlus {n1=Z} LTEZero lte = lte
  ltePlus {n1=S k} LTEZero lte = lteSuccRight $ ltePlus {n1=k} LTEZero lte
  ltePlus (LTESucc lte1) lte2 = LTESucc $ ltePlus lte1 lte2

  lteMult : LTE m1 n1 -> LTE m2 n2 -> LTE (m1 * m2) (n1 * n2)
  lteMult LTEZero _ = LTEZero
  lteMult {m1=S k} (LTESucc _) LTEZero = rewrite multZeroRightZero k in LTEZero
  lteMult (LTESucc lte1) (LTESucc lte2) = LTESucc $ ltePlus lte2 $ lteMult lte1 $ LTESucc lte2

  lteCongMult : (k : Nat) -> LTE m n -> LTE (m * k) (n * k)
  lteCongMult k lte = lteMult lte lteRefl

  lteCongMultLeft : (k : Nat) -> LTE m n -> LTE (k * m) (k * n)
  lteCongMultLeft k lte = lteMult lteRefl lte

%access export
%default total

-- Task 1. Prove that the successor of a Nat cannot be ≤ zero.
notSuccLteZero : Not (S n `LTE` Z)
notSuccLteZero = ?task1

-- Task 2. Prove that you can add any Nat to the right side of a ≤-property.

lteStepK : (k : Nat) -> m `LTE` n -> m `LTE` k + n
lteStepK = ?task2

-- Task 3. Prove that you can remove "addition on the left" from both sides of a ≤-property.

plusLteInjLeft : (a : Nat) -> a + b `LTE` a + c -> b `LTE` c
plusLteInjLeft = ?task3

-- Task 4. Prove that you can remove "multiplication on the left" from both sides of a <-property.

multLtInjLeft : a * b `LT` a * c -> b `LT` c
multLtInjLeft = ?task4

-- Task 5. Prove this.

multLtCross : a * b `LT` c * d -> c `LTE` a -> b `LT` d
multLtCross = ?task5
