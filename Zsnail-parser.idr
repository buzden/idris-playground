import Text.Parser

import Data.Bool

data YamlToken : Type where [external]

Parser : Bool -> Type -> Type
Parser = Grammar (Token YamlToken)

countOcc : {c : Bool} -> Parser c a -> Parser False Nat
countOcc p = rewrite sym $ andFalseFalse (c || False) in
             (S <$ p <*> countOcc p) <|> pure Z
