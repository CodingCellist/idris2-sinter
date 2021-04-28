-- Idris2

module Sinter

import Data.List
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

||| Symbol for indicating membership of namespace: "--|"
specialSep : String
specialSep = "--|"

||| Symbol for indicating record access: "."
recordAcc : String
recordAcc = "."

||| Separate two ids by "specialSep"
stitch : SinterID -> SinterID -> SinterID
stitch (MkSinterID x) (MkSinterID y) = MkSinterID $ x ++ specialSep ++ y

||| Turn a NS into a string separated by "specialSep"
mangleNS : Namespace -> SinterID
mangleNS ns = MkSinterID $ showNSWithSep specialSep ns

||| Sinter doesn't have a concept of NameSpaces, so define unique, but
||| identifiable names/strings instead.
mangle : Name -> SinterID
mangle (NS nameSpace name) =
  let
    nameSpace' = mangleNS nameSpace
    name' = mangle name
  in
    stitch nameSpace' name'

mangle (UN x) = MkSinterID x

mangle (MN x i) = MkSinterID $ x ++ "-" ++ show i

mangle (PV n i) = MkSinterID $ (show $ mangle n) ++ "-" ++ show i

--mangle (DN x y) = MkSinterID x      -- FIXME: correct? (assumes x repr.s y)
mangle (DN _ y) = mangle y            -- ^ incorrect! the Name itself still
                                      -- needs to be mangled; the way to display
                                      -- it doesn't necessarily match our way of
                                      -- representing names.

mangle (RF x) = MkSinterID $ recordAcc ++ x

mangle (Nested (i, j) n) =
  MkSinterID $ "nested_" ++ (show i) ++ "_" ++ (show j) ++ (show $ mangle n)

-- string repr.n of case followed by unique Int (?)
mangle (CaseBlock x i) = MkSinterID $ "case_" ++ x ++ "-" ++ (show i)

mangle (WithBlock x i) = MkSinterID $ "with_" ++ x ++ "-" ++ (show i)

mangle (Resolved i) = MkSinterID $ "resolved_" ++ (show i)


-- Functions

superArgsToSinter : List Name -> List SinterID

liftedToSexpr : Lifted (scope ++ args) -> SinterExpr

--liftedFunToSinter : (name : Name)
--                  -> (args : List Name)
--                  -> (scope : List Name)
--                  -> (sc : Lifted (scope ++ args))
--                  -> Core SinterGlobal
--liftedFunToSinter name args scope sc = ?liftedFunToSinter_rhs


||| Constructors
liftedConToSinter : (name : Name)
                  -> (tag : Maybe Int)
                  -> (arity : Nat)
                  -> (nt : Maybe Nat)
                  -> Core SinterGlobal
liftedConToSinter name tag arity nt = ?liftedConToSinter_rhs


liftedToSinter : (Name, LiftedDef) -> Core SinterGlobal
-- function
liftedToSinter (name, (MkLFun args scope body)) =
  let
    sinName = mangle name
    superArgs = args ++ reverse scope
    sinArgs = superArgsToSinter superArgs
    sinDefn = liftedToSexpr body
  in pure $ SinDef sinName sinArgs sinDefn

-- constructor
liftedToSinter (name, (MkLCon tag arity nt)) =
  liftedConToSinter name tag arity nt

-- ffi call
liftedToSinter (name, (MkLForeign ccs fargs x)) = ?liftedFFICalltoSinter

-- error
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
execute context tmpDir term =
  throw $ InternalError "Sinter backend can only compile, sorry."

sinterCodegen : Codegen
sinterCodegen = MkCG compile execute

main : IO ()
main = mainWithCodegens [("sinter", sinterCodegen)]


