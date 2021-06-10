interface X a where

interface X a => Y a where

[SomeX] X a => X (List a) where

[SomeY] {- X a => -} Y (List a) using SomeX where
