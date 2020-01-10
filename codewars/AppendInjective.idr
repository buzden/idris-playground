module AppendInjective

%access export
%default total

appendInjectiveRight : (a, b, c : List x) -> a ++ b = a ++ c -> b = c
appendInjectiveRight a b c = ?proof1

appendInjectiveLeft : (a, b, c : List x) -> a ++ c = b ++ c -> a = b
appendInjectiveLeft a b c = ?proof2
