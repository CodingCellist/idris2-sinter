module TagList

import Data.List
import Core.Context

public export
TagList : Type
TagList = List Name

append : List a -> a -> List a
append [] y = [y]
append (x :: xs) y = x :: append xs y

public export
find : Eq a => a -> List a -> Maybe Nat
find k [] = Nothing
find k (x :: xs) = case k == x of
                        True  => Just Z
                        False => find k xs >>= (Just . S)

public export
find' : Eq a => a -> List a -> (Nat, List a)
find' k xs = case find k xs of
                  Just v  => (v, xs)
                  Nothing => (length xs, append xs k)
