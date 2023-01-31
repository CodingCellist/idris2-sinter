module TagList

import Data.List
import Core.Context

public export
TagList : Type
TagList = List Name

public export
find' : Eq a => a -> List a -> (Nat, List a)
find' x [] = (Z, [x])
find' x (y :: ys) =
  case (x == y) of
       True  => (Z, y :: ys)
       False => let (i, zs) = find' x ys in (S i, y :: zs)
