-- Idris2

module Sinter

import Data.List
import Data.Vect
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

-- declared here, defined later
data SinterGlobal : Type where

-- an expression is a list of expressions, an ID, or a literal
data Sexpr : Type where
  SexprList : (es : List Sexpr) -> Sexpr
  SexprID : (id_ : SinterID) -> Sexpr
  SexprLit : SinterLit -> Sexpr
  SexprLet : (next : Sexpr) -> (defFun : SinterGlobal) -> Sexpr  -- let-in for sinter

genSexpr : Sexpr -> String
genSexpr (SexprList []) = "[]"

genSexpr (SexprList es) =
  let
    exprs = map genSexpr es
  in sqBrack $ join " " exprs
--  in "[ " ++ (concat exprs) ++ " ]"

genSexpr (SexprID id_) = show id_

genSexpr (SexprLit (SinInt v w)) =
  "( " ++ show v ++ "; " ++ show w ++ " )"

-- TODO
genSexpr (SexprLet next defFun) =
  genSexpr next

Show Sexpr where
  show = genSexpr

-------------------------------
-- Things that can be global --
-------------------------------

-- declared earlier, defined here
data SinterGlobal = SinDef SinterID (List SinterID) Sexpr
                  | SinDecl SinterID (List SinterID)
                  | SinType SinterID (List SinterID)

genSinter : SinterGlobal -> String
genSinter (SinDef fName args body) =
  let
    args' = map show args
    argsStr = sqBrack $ join " " args'
  in sqBrack $ "def " ++ show fName ++ " " ++ argsStr ++ "\n\t"
                ++ genSexpr body

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
                  (SexprList [SexprLit (SinInt 1 2)])



-----------------------
-- Sinter primitives --
-----------------------

sinterPrim : String -> Sexpr
sinterPrim name = SexprID $ MkSinterID name

||| Call the special sinter function for creating closures
sinterClosureCon : Sexpr
sinterClosureCon = sinterPrim ">makeClosure"

||| Call the special sinter function for running or adding args to closures
sinterClosureAdd : Sexpr
sinterClosureAdd = sinterPrim ">closureAddElem"

||| Crash sinter very inelegantly
sinterCrash : Sexpr
sinterCrash = SexprList [ sinterPrim "crash" ]


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


||| Assume < 2^31 number of args to any function (seriously, what would you do
||| with 2^31 args?...)
nArgsWidth : Nat
nArgsWidth = 32

||| Turn all the arguments (including the scope) into SinterIDs
superArgsToSinter : List Name -> List SinterID
superArgsToSinter ns = map mangle ns


mutual
  -- Primitive Functions

  primFnToSexpr : {scope : _} -> {args : _}
                -> PrimFn arity -> Vect arity (Lifted (scope ++ args)) -> Sexpr
  primFnToSexpr (Add ty) [x, y] =
    SexprList [ sinterPrim "add", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (Sub ty) [x, y] =
    SexprList [ sinterPrim "sub", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (Mul ty) [x, y] =
    SexprList [ sinterPrim "mul", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (Div ty) [x, y] =
    SexprList [ sinterPrim "div", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (Mod ty) [x, y] =
    SexprList [ sinterPrim "mod", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (Neg ty) [x] =
    SexprList [ sinterPrim "neg", liftedToSexpr x ]

  primFnToSexpr (ShiftL ty) [x, y] =
    SexprList [ sinterPrim "shiftl", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (ShiftR ty) [x, y] =
    SexprList [ sinterPrim "shiftr", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (BAnd ty) [x, y] =
    SexprList [ sinterPrim "bitwAnd", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (BOr ty) [x, y] =
    SexprList [ sinterPrim "bitwOr", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (BXOr ty) [x, y] =
    SexprList [ sinterPrim "bitwXor", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (LT ty) [x, y] =
    SexprList [ sinterPrim "lt", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (LTE ty) [x, y] =
    SexprList [ sinterPrim "lte", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (EQ ty) [x, y] =
    SexprList [ sinterPrim "eq", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (GTE ty) [x, y] =
    SexprList [ sinterPrim "gte", liftedToSexpr x, liftedToSexpr y ]

  primFnToSexpr (GT ty) [x, y] =
    SexprList [ sinterPrim "gt", liftedToSexpr x, liftedToSexpr y ]

  -- TODO
  primFnToSexpr StrLength xs = ?primFnToSexpr_rhs_17
  primFnToSexpr StrHead xs = ?primFnToSexpr_rhs_18
  primFnToSexpr StrTail xs = ?primFnToSexpr_rhs_19
  primFnToSexpr StrIndex xs = ?primFnToSexpr_rhs_20
  primFnToSexpr StrCons xs = ?primFnToSexpr_rhs_21
  primFnToSexpr StrAppend xs = ?primFnToSexpr_rhs_22
  primFnToSexpr StrReverse xs = ?primFnToSexpr_rhs_23
  primFnToSexpr StrSubstr xs = ?primFnToSexpr_rhs_24

  -- TODO
  primFnToSexpr DoubleExp xs = ?primFnToSexpr_rhs_25
  primFnToSexpr DoubleLog xs = ?primFnToSexpr_rhs_26
  primFnToSexpr DoubleSin xs = ?primFnToSexpr_rhs_27
  primFnToSexpr DoubleCos xs = ?primFnToSexpr_rhs_28
  primFnToSexpr DoubleTan xs = ?primFnToSexpr_rhs_29
  primFnToSexpr DoubleASin xs = ?primFnToSexpr_rhs_30
  primFnToSexpr DoubleACos xs = ?primFnToSexpr_rhs_31
  primFnToSexpr DoubleATan xs = ?primFnToSexpr_rhs_32
  primFnToSexpr DoubleSqrt xs = ?primFnToSexpr_rhs_33
  primFnToSexpr DoubleFloor xs = ?primFnToSexpr_rhs_34
  primFnToSexpr DoubleCeiling xs = ?primFnToSexpr_rhs_35

  -- TODO
  primFnToSexpr (Cast x y) [z] = ?primFnToSexpr_rhs_36
  primFnToSexpr BelieveMe [_, _, thing] = liftedToSexpr thing
                                        -- ^ I believe this is correct?

  primFnToSexpr Crash [fc, reason] =
    sinterCrash

  ||| Create a call to a function which evaluates `in` over `let`
  |||   let f x = y in z
  |||   is equivalent to
  |||   (\f . z) (\x . y)
  lletToSexpr : {scope : _} -> {args : _}
              -> FC
              -> (n : Name)
              -> (existing : Lifted (scope ++ args))
              -> (in_expr : Lifted (n :: (scope ++ args)))
              -> Sexpr
  lletToSexpr fc n existing in_expr =
    let
      -- containing IN
      vars = scope ++ args
      cursedFuncName = show fc ++ show n
      cFunName = MkSinterID cursedFuncName
      cFunArgs = (mangle n) :: map mangle vars
      -- scope' = n :: scope      -- v doesn't work here
      cFunBody = liftedToSexpr {scope=(n :: scope)} {args=args} in_expr
      cFunDef = SinDef cFunName cFunArgs cFunBody

      -- applying this
      cFunCallArgs = liftedToSexpr {scope=scope} {args=args} existing
      cFunCall = SexprList $ (SexprID cFunName)
                             :: cFunCallArgs
                             :: (map (SexprID . mangle) vars)
    in
      SexprLet cFunCall cFunDef

  -- Functions

  ||| Compile the definition to sexprs
  liftedToSexpr : {scope : _} -> {args : _} -> Lifted (scope ++ args) -> Sexpr
  liftedToSexpr (LLocal {idx} fc p) = ?fcToSexpr

  -- complete function call
  liftedToSexpr (LAppName fc _ n fArgs) =
    let
      funName = SexprID $ mangle n
      funArgs = map (liftedToSexpr {scope=scope} {args=args}) fArgs
    in
      SexprList $ funName :: funArgs

  -- partial function call
  liftedToSexpr (LUnderApp fc n missing fArgs) =
    let
      sinName  = SexprID $ mangle n
      sinMiss  = SexprLit $ SinInt (cast missing) nArgsWidth
      nArgs    = length args
      sinNArgs = SexprLit $ SinInt (cast nArgs) nArgsWidth
      -- number of args function expects
      sinArity = SexprLit $ SinInt (cast (missing + nArgs)) nArgsWidth
      -- list of arguments
      --sinArgs  = SexprList $ map liftedToSexpr fArgs
      sinArgs  = SexprList $ map (liftedToSexpr {scope=scope} {args=args}) fArgs
    in
      -- make a closure containing the above info (sinter-specific closure)
      SexprList [sinterClosureCon , sinName , sinArity , sinNArgs , sinArgs]

  -- application of a closure to another argument; potentially to the last arg
  liftedToSexpr (LApp fc _ closure arg) =
    let
      sinClosure = liftedToSexpr closure
      sinArg = liftedToSexpr arg
    in
      SexprList [sinterClosureAdd, sinClosure, sinArg]

  -- let a = b in c
  -- \l c . (\f a . b) c

  -- [ def fun [ a c ]
  --           [ fun2 a c b ] ]
  liftedToSexpr (LLet fc n existing in_expr) = lletToSexpr fc n existing in_expr

  liftedToSexpr (LCon fc n tag xs) = ?liftedToSexpr_rhs_6

  liftedToSexpr (LOp fc _ x xs) = primFnToSexpr x xs

  liftedToSexpr (LExtPrim fc _ p xs) = ?liftedToSexpr_rhs_8
  liftedToSexpr (LConCase fc x xs y) = ?liftedToSexpr_rhs_9
  liftedToSexpr (LConstCase fc x xs y) = ?liftedToSexpr_rhs_10
  liftedToSexpr (LPrimVal fc x) = ?liftedToSexpr_rhs_11
  liftedToSexpr (LErased fc) = ?liftedToSexpr_rhs_12

  liftedToSexpr (LCrash fc x) =
    sinterCrash


||| Compile a constructor's definition
liftedConToSinter : (tag : Maybe Int)
                  -> (arity : Nat)
                  -> (nt : Maybe Nat)
                  -> Core SinterGlobal
liftedConToSinter tag arity nt = ?liftedConToSinter_rhs


||| Compile a pair of Name and its associated definition into a SinterGlobal,
||| i.e.:
|||   - mangle the Name into a valid sinter name
|||   - compile the definition into a sexpr
liftedToSinter : (Name, LiftedDef) -> Core SinterGlobal

-- FUNCTIONS
liftedToSinter (name, (MkLFun args scope body)) =
  let
    sinName = mangle name
    superArgs = args ++ reverse scope
    sinArgs = superArgsToSinter superArgs
    sinDefn = liftedToSexpr body
  in
    pure $ SinDef sinName sinArgs sinDefn

-- CONSTRUCTORS
liftedToSinter (name, (MkLCon tag arity nt)) =
  let
    sinName = mangle name
    sinDefn = liftedConToSinter tag arity nt
  in
    pure $ SinType sinName ?liftedConBody

-- FFI CALLS
liftedToSinter (name, (MkLForeign ccs fargs x)) = ?liftedFFICalltoSinter

-- GLOBAL ERRORS
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

