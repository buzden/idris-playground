module Sprintf

%access export
%default total

public export
data Sty : Type -> Type where
  Nil          : Sty String
  Ordinary     : (k : Char) -> (tl : Sty t) -> Sty t
  IntDemand    :               (tl : Sty t) -> Sty (Integer -> t)
  DoubleDemand :               (tl : Sty t) -> Sty (Double -> t)
  CharDemand   :               (tl : Sty t) -> Sty (Char -> t)
  BadDemand    :               (tl : Sty t) -> Sty (Void -> t)

public export
strToSty : (str : List Char) -> (t : Type ** Sty t)
strToSty []             =                                 (_ ** Nil)
strToSty ('%'::Nil)     =                                 (_ ** BadDemand Nil)
strToSty ('%'::'%'::ks) = let (_ ** sub) = strToSty ks in (_ ** Ordinary '%' sub)
strToSty ('%'::'d'::ks) = let (_ ** sub) = strToSty ks in (_ ** IntDemand sub)
strToSty ('%'::'f'::ks) = let (_ ** sub) = strToSty ks in (_ ** DoubleDemand sub)
strToSty ('%'::'c'::ks) = let (_ ** sub) = strToSty ks in (_ ** CharDemand sub)
strToSty ('%':: _ ::ks) = let (_ ** sub) = strToSty ks in (_ ** BadDemand sub)
strToSty ( k :: ks)     = let (_ ** sub) = strToSty ks in (_ ** Ordinary k sub)

public export
sprintf' : List Char -> Sty t -> t
sprintf' c []                = pack $ reverse c
sprintf' c (Ordinary k tl)   = sprintf' (k::c) tl
sprintf' c (IntDemand tl)    = \n => sprintf' (unpack (show n) ++ c) tl
sprintf' c (DoubleDemand tl) = \x => sprintf' (unpack (show x) ++ c) tl
sprintf' c (CharDemand tl)   = \k => sprintf' (k::c) tl
sprintf' c (BadDemand tl)    = void

public export
sprintf : (str : String) -> fst $ strToSty $ unpack str
sprintf str = sprintf' [] $ snd $ strToSty $ unpack str
