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
evenPlusOne (NextEven n) = NextOdd $ evenPlusOne n

-- | Proves that if n is odd, n+1 is even.
oddPlusOne : Odd n -> Even (S n)
oddPlusOne  OneOdd     = NextEven $ ZeroEven
oddPlusOne (NextOdd n) = NextEven $ oddPlusOne n

-- | Proves even + even = even
evenPlusEven : Even n -> Even m -> Even (n + m)
evenPlusEven  ZeroEven    m = m
evenPlusEven (NextEven n) m = NextEven $ evenPlusEven n m

-- | Proves odd + odd = even
oddPlusOdd : Odd n -> Odd m -> Even (n + m)
oddPlusOdd = ?oddPlusOdd_rhs

-- | Proves even + odd = odd
evenPlusOdd : Even n -> Odd m -> Odd (n + m)
evenPlusOdd = ?evenPlusOdd_rhs

-- | Proves odd + even = odd
oddPlusEven : Odd n -> Even m -> Odd (n + m)
oddPlusEven = ?oddPlusEven_rhs

-- | Proves even * even = even
evenTimesEven : Even n -> Even m -> Even (n * m)
evenTimesEven = ?evenTimesEven_rhs

-- | Proves odd * odd = odd
oddTimesOdd : Odd n -> Odd m -> Odd (n * m)
oddTimesOdd = ?oddTimesOdd_rhs

-- | Proves even * odd = even
evenTimesOdd : Even n -> Odd m -> Even (n * m)
evenTimesOdd = ?evenTimesOdd_rhs

-- | Proves odd * even = even
oddTimesEven : Odd n -> Even m -> Even (n * m)
oddTimesEven = ?oddTimesEven_rhs

