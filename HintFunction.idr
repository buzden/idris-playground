module HintFunction

import Data.Fuel

import HintFunctionGen

export %hint
listOfLim : Fuel -> Gen a => Gen (List a)
listOfLim Dry      @{genA} = pure [] <|> pure <$> genA
listOfLim (More f) @{genA} = let sub = listOfLim f in sub <|> [| genA :: sub |]

export
al : (Fuel -> Gen (List a)) => Gen a
al @{genList} = do
  xs <- genList $ limit 2
  choiceMap pure xs

export
al' : (Fuel -> Gen (List Int)) => String
al' @{genList} = show $ genList $ limit 2

export %hint
genNat : Gen Int
genNat = pure 0 <|> pure 1

export
xx : Gen Int
xx = al

export
yy : String
yy = al' -- @{listOfLim}
