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

sprintf' : List Char -> (str : List Char) -> SprintfType str
sprintf' curr []                   = curr
sprintf' curr ('%' :: '%' :: rest) = sprintf' (curr ++ ['%']) rest
sprintf' curr ('%' :: 'd' :: rest) = \n => sprintf' (curr ++ unpack (show n)) rest
sprintf' curr ('%' :: 'f' :: rest) = \n => sprintf' (curr ++ unpack (show n)) rest
sprintf' curr ('%' :: 'c' :: rest) = \n => sprintf' (curr ++ unpack (show n)) rest
--sprintf' curr ('%' :: _)           = void
sprintf' curr (k   :: rest)        = ?sp_rhs -- sprintf' (curr ++ [k]) rest

--sprintf : (str : String) -> SprintfType (unpack str)
--sprintf = pack . sprintf' [] . unpack
