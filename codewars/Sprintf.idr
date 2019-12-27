module Sprintf

%access export
%default total

public export
SprintfType : String -> Type
SprintfType x = case strM x of
  StrNil => String
  ('%' `StrCons` qual) => case strM qual of
    ('%' `StrCons` rest) => SprintfType rest
    ('d' `StrCons` rest) => Integer -> SprintfType rest
    ('f' `StrCons` rest) => Double  -> SprintfType rest
    ('c' `StrCons` rest) => Char    -> SprintfType rest
    _                    => Void    -> String
  (_ `StrCons` rest) => SprintfType rest

sprintf' : String -> (str : String) -> SprintfType str
sprintf' curr str with (strM str)
  sprintf' curr "" | StrNil = curr
  | ('%' `StrCons` qual) with (strM qual)
    | _ | ('%' `StrCons` rest) = sprintf (curr ++ "%") rest
    | _ | ('d' `StrCons` rest) = \n => sprintf (curr ++ show n) rest
    | _ | ('f' `StrCons` rest) = \n => sprintf (curr ++ show n) rest
    | _ | ('c' `StrCons` rest) = \n => sprintf (curr ++ show n) rest
    | _ | _                    = \n => absurd n
  | (k `StrCons` rest) = sprintf (curr ++ singleton k) rest

sprintf : (str : String) -> SprintfType str
sprintf = sprintf' ""
