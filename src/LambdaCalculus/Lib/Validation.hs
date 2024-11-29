module LambdaCalculus.Lib.Validation where

import Data.Validation

note :: e -> Maybe a -> Validation e a
note e = maybe (Failure e) Success
