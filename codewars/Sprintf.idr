module Sprintf

import Data.String

%default total

public export
strToSty : (curr : String) -> (str : List Char) -> (t : Type ** t)
strToSty c []             = (_ ** c)
strToSty c ('%'::'%'::ks) = strToSty (c ++ "%") ks
strToSty c ('%'::'d'::ks) = (_ ** \n : Integer => snd $ strToSty (c ++ show n) ks)
strToSty c ('%'::'f'::ks) = (_ ** \x : Double  => snd $ strToSty (c ++ show x) ks)
strToSty c ('%'::'c'::ks) = (_ ** \k : Char    => snd $ strToSty (c ++ singleton k) ks)
strToSty c ('%':: ks)     = (_ ** \v : Void    => snd $ strToSty c ks)
strToSty c ( k :: ks)     = strToSty (c ++ singleton k) ks

export
sprintf : (str : String) -> fst (strToSty "" $ unpack str)
sprintf str = snd (strToSty "" $ unpack str)
