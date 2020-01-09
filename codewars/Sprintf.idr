module Sprintf

%access export
%default total

public export
strToSty : (curr : List Char) -> (str : List Char) -> (t : Type ** t)
strToSty c []             = (_ ** pack $ reverse c)
strToSty c ('%'::'%'::ks) = strToSty ('%'::c) ks
strToSty c ('%'::'d'::ks) = (_ ** \n : Integer => snd $ strToSty (unpack (show n) ++ c) ks)
strToSty c ('%'::'f'::ks) = (_ ** \x : Double  => snd $ strToSty (unpack (show x) ++ c) ks)
strToSty c ('%'::'c'::ks) = (_ ** \k : Char    => snd $ strToSty (k::c) ks)
strToSty c ('%':: ks)     = (_ ** \v : Void    => snd $ strToSty c ks)
strToSty c ( k :: ks)     = strToSty (k::c) ks

public export
sprintf : (str : String) -> fst (strToSty [] $ unpack str)
sprintf str = snd (strToSty [] $ unpack str)
