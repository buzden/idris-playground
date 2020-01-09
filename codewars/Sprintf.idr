module Sprintf

%access export
%default total

public export
SprintfType : List Char -> Type
SprintfType []                   =            List Char
SprintfType ('%' :: Nil)         = Void    -> List Char
SprintfType ('%' :: '%' :: rest) =            SprintfType rest
SprintfType ('%' :: 'd' :: rest) = Integer -> SprintfType rest
SprintfType ('%' :: 'f' :: rest) = Double  -> SprintfType rest
SprintfType ('%' :: 'c' :: rest) = Char    -> SprintfType rest
SprintfType ('%' :: _   :: rest) = Void    -> SprintfType rest
SprintfType (_   :: rest)        =            SprintfType rest

public export
data Sty : Type -> Type where
  Nil          : Sty (List Char)
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

sprintf' : List Char -> Sty t -> t
sprintf' c []                = reverse c
sprintf' c (Ordinary k tl)   = sprintf' (k::c) tl
sprintf' c (IntDemand tl)    = \n => sprintf' (unpack (show n) ++ c) tl
sprintf' c (DoubleDemand tl) = \x => sprintf' (unpack (show x) ++ c) tl
sprintf' c (CharDemand tl)   = \k => sprintf' (k::c) tl
sprintf' c (BadDemand tl)    = void

sprintf : (str : String) -> {default (strToSty str) sty : Sty t} -> t
sprintf str {sty} = sprintf' [] sty
