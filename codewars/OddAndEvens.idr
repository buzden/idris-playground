module OddAndEvens

%access export
%default total

public export
data Even : Nat -> Type where
  -- | Zero is even.
  ZeroEven : Even Z
  -- | If n is even, then n+2 is even.
  NextEven : Even n -> Even (S (S n))

public export
data Odd : Nat -> Type where
  -- | One is odd.
  OneOdd : Odd (S Z)
  -- | If n is odd, then n+2 is odd.
  NextOdd : Odd n -> Odd (S (S n))

-- | Proves that if n is even, n+1 is odd.
-- Notice how I use the axioms here.
evenPlusOne : Even n -> Odd (S n)
evenPlusOne  ZeroEven    = OneOdd
evenPlusOne (NextEven x) = NextOdd $ evenPlusOne x

-- | Proves that if n is odd, n+1 is even.
oddPlusOne : Odd n -> Even (S n)
oddPlusOne  OneOdd     = NextEven $ ZeroEven
oddPlusOne (NextOdd x) = NextEven $ oddPlusOne x

-- | Proves even + even = even
evenPlusEven : Even n -> Even m -> Even (n + m)
evenPlusEven  ZeroEven    y = y
evenPlusEven (NextEven x) y = NextEven $ evenPlusEven x y

-- | Proves odd + odd = even
oddPlusOdd : Odd n -> Odd m -> Even (n + m)
oddPlusOdd OneOdd      y = oddPlusOne y
oddPlusOdd (NextOdd x) y = NextEven $ oddPlusOdd x y

-- | Proves even + odd = odd
evenPlusOdd : Even n -> Odd m -> Odd (n + m)
evenPlusOdd ZeroEven     y = y
evenPlusOdd (NextEven x) y = NextOdd $ evenPlusOdd x y

-- | Proves odd + even = odd
oddPlusEven : Odd n -> Even m -> Odd (n + m)
oddPlusEven OneOdd      y = evenPlusOne y
oddPlusEven (NextOdd x) y = NextOdd $ oddPlusEven x y

-- | Proves even * even = even
evenTimesEven : Even n -> Even m -> Even (n * m)
evenTimesEven ZeroEven     _ = ZeroEven
evenTimesEven (NextEven x) y = evenPlusEven y $ evenPlusEven y $ evenTimesEven x y

-- | Proves odd * odd = odd
oddTimesOdd : Odd n -> Odd m -> Odd (n * m)
oddTimesOdd OneOdd {m}  y = rewrite plusZeroRightNeutral m in y
oddTimesOdd (NextOdd x) y = oddPlusEven y $ oddPlusOdd y $ oddTimesOdd x y

-- | Proves even * odd = even
evenTimesOdd : Even n -> Odd m -> Even (n * m)
evenTimesOdd ZeroEven y = ZeroEven
evenTimesOdd (NextEven x) y = oddPlusOdd y $ oddPlusEven y $ evenTimesOdd x y

-- | Proves odd * even = even
oddTimesEven : Odd n -> Even m -> Even (n * m)
oddTimesEven OneOdd {m}  y = rewrite plusZeroRightNeutral m in y
oddTimesEven (NextOdd x) y = evenPlusEven y $ evenPlusEven y $ oddTimesEven x y
