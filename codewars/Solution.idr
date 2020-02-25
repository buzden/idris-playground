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
notSuccLteZero LTEZero impossible

-- Task 2. Prove that you can add any Nat to the right side of a ≤-property.

lteStepK : (k : Nat) -> m `LTE` n -> m `LTE` k + n
lteStepK _ = ltePlus LTEZero

-- Task 3. Prove that you can remove "addition on the left" from both sides of a ≤-property.

plusLteInjLeft : (a : Nat) -> a + b `LTE` a + c -> b `LTE` c
plusLteInjLeft Z     abc         = abc
plusLteInjLeft (S k) (LTESucc x) = plusLteInjLeft k x

-- Task 4. Prove that you can remove "multiplication on the left" from both sides of a <-property.

succGoesOut : (x, y, a : Nat) -> x + a * (S y) = a + (x + a * y)
succGoesOut x y a = rewrite multRightSuccPlus a y in
                    rewrite plusCommutative x $ a + (a*y) in
                    rewrite sym $ plusAssociative a (a*y) x in
                    rewrite plusCommutative (a*y) x in
                    Refl

multLtInjLeft : a * b `LT` a * c -> b `LT` c
multLtInjLeft {a=Z}   {b}     {c}     = \LTEZero impossible
multLtInjLeft {a=S a} {b=Z}   {c=Z}   = rewrite multZeroRightZero a in id
multLtInjLeft {a=S a} {b=Z}   {c=S c} = \_ => LTESucc LTEZero
multLtInjLeft {a=S a} {b=S b} {c=Z}   = rewrite multZeroRightZero a in \LTEZero impossible
multLtInjLeft {a=S a} {b=S b} {c=S c} = rewrite succGoesOut b b a in
                                        rewrite succGoesOut c c a in
                                        rewrite plusSuccRightSucc a $ b + a*b in
                                        \(LTESucc lt) => LTESucc . multLtInjLeft {a=S a} $ plusLteInjLeft a lt

-- Task 5. Prove this.

lteDelta : x `LTE` y -> (d ** x + d = y)
lteDelta {y} LTEZero = (y ** Refl)
lteDelta {x=S x} {y=S y} (LTESucc lte) = (_ ** cong {f=S} $ snd $ lteDelta lte)

lteCutLeft : c + a `LTE` b -> a `LTE` b
lteCutLeft {c=Z}   = id
lteCutLeft {c=S k} = lteCutLeft . lteSuccLeft

multLtCross'delta : (delta : Nat ** c + delta = a) -> a * b `LT` c * d -> b `LT` d
multLtCross'delta (delta ** prf) {b} {c} =
  rewrite sym prf in
  rewrite plusCommutative c delta in
  rewrite multDistributesOverPlusLeft delta c b in
  rewrite plusSuccRightSucc (delta * b) (c * b) in
  multLtInjLeft . lteCutLeft

multLtCross : a * b `LT` c * d -> c `LTE` a -> b `LT` d
multLtCross {a} {c} abcd ca = let (delta ** prf) = lteDelta ca in
                              multLtCross'delta (lteDelta ca) abcd
