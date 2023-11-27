import Data.Vect

import Decidable.Equality

namespace VectsReturned

  JSON : Type
  Record : JSON -> Type

  parseJSON : (json : JSON) -> Either String (n ** Vect n $ Record json)

  mergeParsedJSONs : (one, another : JSON) -> (merger : Record one -> Record another -> a) -> Either String (n ** Vect n a)
  mergeParsedJSONs one another merger = do
    (rn ** rs) <- parseJSON one
    (sn ** ss) <- parseJSON another
    let Yes Refl = decEq rn sn
      | No _ => Left "Lengths are not equal: \{show rn} vs. \{show sn}"
    pure $ (_ ** zipWith merger rs ss)

namespace VectsHidden

  JSON : Type
  Record : JSON -> Type

  parseJSON : (json : JSON) -> Either String $ List $ Record json

  mergeParsedJSONs : (one, another : JSON) -> (merger : Record one -> Record another -> a) -> Either String $ List a
  mergeParsedJSONs one another merger = do
    rs <- parseJSON one
    ss <- parseJSON another
    let Yes lengthsEq = decEq (length rs) (length ss)
      | No _ => Left "Lengths are not equal: \{show $ length rs} vs. \{show $ length ss}"
    pure $ toList $ zipWith merger (fromList rs) (rewrite lengthsEq in fromList ss)
