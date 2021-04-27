-- Idris2

module Sinter

import Data.String.Extra

import Core.Context
import Compiler.LambdaLift
import Compiler.Common
import Idris.Driver

------------
-- SINTER --
------------

sqBrack : String -> String
sqBrack s = "[ " ++ s ++ " ]"

-- only literals in sinter are ints
data SinterLit
  = SinInt Int Nat    -- Int is value then width

-- IDs are basically strings (not really, TODO)
data SinterID = MkSinterID String

genSinterID : SinterID -> String
genSinterID (MkSinterID id_) = id_

Show SinterID where
  show = genSinterID

-- an expression is a list of expressions, an ID, or a literal
data SinterExpr : Type where
  SinterExprList : (es : List SinterExpr) -> SinterExpr
  SinterExprID : (id_ : SinterID) -> SinterExpr
  SinterExprLit : SinterLit -> SinterExpr

genSinterExpr : SinterExpr -> String
genSinterExpr (SinterExprList []) = "[]"

genSinterExpr (SinterExprList es) =
  let
    exprs = map genSinterExpr es
  in sqBrack $ join " " exprs
--  in "[ " ++ (concat exprs) ++ " ]"

genSinterExpr (SinterExprID id_) = show id_

genSinterExpr (SinterExprLit (SinInt v w)) =
  "( " ++ show v ++ "; " ++ show w ++ " )"

Show SinterExpr where
  show = genSinterExpr

data SinterGlobal = SinDef SinterID (List SinterID) SinterExpr
                  | SinDecl SinterID (List SinterID)
                  | SinType SinterID (List SinterID)

genSinter : SinterGlobal -> String
genSinter (SinDef fName args body) =
  let
    args' = map show args
    argsStr = sqBrack $ join " " args'
  in sqBrack $ "def " ++ show fName ++ " " ++ argsStr ++ "\n\t"
                ++ genSinterExpr body

genSinter (SinDecl fName args) =
  let
    args' = map show args
    argsStr = sqBrack $ join " " args'
  in sqBrack $ "dec " ++ show fName ++ " " ++ argsStr

genSinter (SinType tName membs) = ?genSinter_rhs_3
  let
    membs' = map show membs
    membsStr = sqBrack $ join " " membs'
  in sqBrack $ "type " ++ show tName ++ membsStr

Show SinterGlobal where
  show = genSinter


testCase : SinterGlobal
testCase = SinDef (MkSinterID "test") [(MkSinterID "arg1"), (MkSinterID "arg2")]
                  (SinterExprList [SinterExprLit (SinInt 1 2)])

------------------
-- GORY DETAILS --
------------------

liftedFunToSinter : (name : Name)
                  -> (scope : List Name)
                  -> (args : List Name)
                  -> (x : Lifted (scope ++ args))
                  -> ?hole2

liftedToSinter : (Name, LiftedDef) -> ?hole
liftedToSinter (name, (MkLFun args scope x)) = liftedFunToSinter name scope args x
liftedToSinter (name, (MkLCon tag arity nt)) = ?liftedConToSinter
liftedToSinter (name, (MkLForeign ccs fargs x)) = ?liftedFFItoSinter
liftedToSinter (name, (MkLError x)) = ?liftedErrorToSinter


----------------
-- TOP OF API --
----------------

compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
        ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile context tmpDir outputDir term outfile =
  do compData <- getCompileData False Lifted term
     let defs = lambdaLifted compData
     ?compile_rhs

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute context tmpDir term = ?execute_rhs

sinterCodegen : Codegen
sinterCodegen = MkCG compile execute

main : IO ()
main = mainWithCodegens [("sinter", sinterCodegen)]


