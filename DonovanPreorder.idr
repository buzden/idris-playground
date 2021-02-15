-- My answer to the question in Slack https://functionalprogramming.slack.com/archives/C043A0KTY/p1613365432408100

import Syntax.PreorderReasoning

import Data.Nat

mult_plus_distr : (n, m, p : Nat) -> (n + m) * p = (n * p) + (m * p)
mult_plus_distr 0 m p = Refl
mult_plus_distr (S k) m p =
  let ih = mult_plus_distr k m p
  in rewrite ih in plusAssociative p (mult k p) (mult m p)

mult_assoc : (n, m, p : Nat) -> n * (m * p) = (n * m) * p
mult_assoc Z m p = Refl
mult_assoc (S k) m p = Calc $
  |~ (S k) * (m * p)
  ~~ (m * p) + k * (m * p) ... ( Refl )
  ~~ (m * p) + (k * m) * p ... ( cong ((m * p) +) $ mult_assoc k m p )
  ~~ (m + k * m) * p       ... ( sym $ mult_plus_distr m (k * m) p )
