-- vim: tw=80 sw=2 ts=2 et

||| Contains types to desribe Sinter syntax trees, and functions for
||| converting those trees into text.
module Sinter

import Data.String.Extra -- for join
import Data.String -- for lines

sExpr : String -> String -> String
sExpr v w = "(" ++ v ++ ";" ++ w ++ ")"

||| Takes a list of strings and put them in a single string in
||| M-expression format (semicolon-separated and surrounded with square
||| brackets).
mExpr : Foldable f => f String -> String
mExpr xs = "[" ++ (join ";" xs) ++ "]"

||| Denotes a literal value for the Sinter source.
public export
data SinterLiteral
  = SinterInt Int Nat -- Int is value, Nat is bit width
  | SinterStr String

||| Denotes an identifier (as in, a name to reference another, possibly
||| calculated, value) for the Sinter source.
public export
data SinterID
  = MkSinterID String

public export
(++) : SinterID -> SinterID -> SinterID
(++) (MkSinterID a) (MkSinterID b) = MkSinterID (a ++ b)

||| Converts a Sinter ID to its text representation.
genSID : SinterID -> String
genSID (MkSinterID id') = id'

||| Takes a list of Sinter IDs and combines them into a single string
||| in M-expression format.
mExprSID : List SinterID -> String
mExprSID ids = mExpr $ map genSID ids

||| Represents an expression in Sinter source.
|||
||| Expressions in sinter can be literals, IDs, or lists of
||| other expressions.
public export
data SinterExpr : Type where
  SinterList : Foldable f => Functor f => f SinterExpr -> SinterExpr
  SinterPair : (SinterExpr, SinterExpr) -> SinterExpr
  SinterLiteralExpr : SinterLiteral -> SinterExpr
  SinterExprID : SinterID -> SinterExpr

||| Render a Sinter expression into text.
genSexpr : SinterExpr -> String
genSexpr (SinterList exprs) = mExpr $ map genSexpr exprs

genSexpr (SinterPair (x, y)) = sExpr (genSexpr x) (genSexpr y)

genSexpr (SinterLiteralExpr expr) = case expr of
  SinterInt v w => sExpr (show v) (show w)
  SinterStr v => show v

genSexpr (SinterExprID id') = genSID id'

-- can't implement Show with genSexpr since genSexpr isn't proven to be total

public export
data SinterTopLevel
  = SinterDef SinterID (List SinterID) SinterExpr
  | SinterDec SinterID (List SinterID)
  | SinterType SinterID (List SinterID)

genTopLevel : SinterTopLevel -> String
genTopLevel (SinterDef id' ns ex)
  = mExpr [ "def", genSID id', mExprSID ns, genSexpr ex ] ++ "\n"

genTopLevel (SinterDec id' ns)
  = mExpr [ "dec", genSID id', mExprSID ns ] ++ "\n"

genTopLevel (SinterType id' ns)
  = mExpr [ "type", genSID id', mExprSID ns ] ++ "\n"

reverseTopLevel : List SinterTopLevel -> List SinterTopLevel
reverseTopLevel = reverse

public export
gen : List SinterTopLevel -> String
gen xs = concatMap genTopLevel $ reverse xs

