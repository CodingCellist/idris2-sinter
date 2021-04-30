-- Idris2

module Sinter.ANF

import Data.List
import Data.Vect
import Data.String.Extra

import Core.Context
import Core.CompileExpr

import Compiler.ANF
import Compiler.Common
import Idris.Driver

------------
-- SINTER --
------------

sqBrack : String -> String
sqBrack s = "[ " ++ s ++ " ]"

-- only literals in sinter are ints
data SinterLit
  = SinInt Int Nat    -- TODO: Int is value then width
  | SinStr String

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
  "( " ++ show w ++ "; " ++ show v ++ " )"

genSexpr (SexprLit (SinStr s)) =
  show s

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

genSinter (SinType tName membs) =
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

||| Primitive implemented in sinter
sinterPrim : String -> Sexpr
sinterPrim name = SexprID $ MkSinterID name

||| Primitive supplied by stdlib
sinterStdlib : String -> Sexpr
sinterStdlib name = SexprID $ MkSinterID ("stdlib_" ++ name)

||| Call the special sinter function for creating closures
sinterClosureCon : Sexpr
sinterClosureCon = sinterPrim ">makeClosure"

||| Call the special sinter function for running or adding args to closures
sinterClosureAdd : Sexpr
sinterClosureAdd = sinterPrim ">closureAddElem"

||| Crash sinter very inelegantly
sinterCrash : Sexpr
sinterCrash = SexprList [ sinterPrim "CRASH" ]


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


idrisWorld : Sexpr
idrisWorld = SexprID $ MkSinterID "**IDRIS_WORLD**"

||| Assume < 2^31 number of args to any function (seriously, what would you do
||| with 2^31 args?...)
nArgsWidth : Nat
nArgsWidth = 32

||| Turn all the arguments (including the scope) into SinterIDs
superArgsToSinter : List Name -> List SinterID
superArgsToSinter ns = map mangle ns


-- Constants

constantToSexpr : Constant -> Sexpr
constantToSexpr (I x) = ?sexprConstI
constantToSexpr (BI x) = ?sexprConstBI
constantToSexpr (B8 x) = SexprLit $ SinInt (cast x) 8
constantToSexpr (B16 x) = SexprLit $ SinInt (cast x) 16
constantToSexpr (B32 x) = SexprLit $ SinInt (cast x) 32
constantToSexpr (B64 x) = SexprLit $ SinInt (cast x) 64
constantToSexpr (Str x) = SexprLit $ SinStr x
constantToSexpr (Ch x) = ?constantToSexpr_rhs_8
constantToSexpr (Db x) = ?constantToSexpr_rhs_9
constantToSexpr WorldVal = idrisWorld
constantToSexpr IntType = ?constantToSexpr_rhs_11
constantToSexpr IntegerType = ?constantToSexpr_rhs_12
constantToSexpr Bits8Type = ?constantToSexpr_rhs_13
constantToSexpr Bits16Type = ?constantToSexpr_rhs_14
constantToSexpr Bits32Type = ?constantToSexpr_rhs_15
constantToSexpr Bits64Type = ?constantToSexpr_rhs_16
constantToSexpr StringType = ?constantToSexpr_rhs_17
constantToSexpr CharType = ?constantToSexpr_rhs_18
constantToSexpr DoubleType = ?constantToSexpr_rhs_19
constantToSexpr WorldType = ?constantToSexpr_rhs_20


intNameToSinterID : Int -> SinterID
intNameToSinterID i = MkSinterID $ "a" ++ show i


aVarToSexpr : AVar -> Sexpr
aVarToSexpr (ALocal i) = SexprID $ intNameToSinterID i
aVarToSexpr ANull = SexprLit $ SinInt 0 1

mutual
  -- Primitive Functions

  primFnToSexpr : PrimFn arity -> Vect arity AVar -> Sexpr
  primFnToSexpr (Add ty) [x, y] =
    SexprList [ sinterStdlib "add", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (Sub ty) [x, y] =
    SexprList [ sinterStdlib "sub", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (Mul ty) [x, y] =
    SexprList [ sinterStdlib "mul", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (Div ty) [x, y] =
    SexprList [ sinterStdlib "div", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (Mod ty) [x, y] =
    SexprList [ sinterStdlib "mod", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (Neg ty) [x] =
    SexprList [ sinterStdlib "neg", aVarToSexpr x ]

  primFnToSexpr (ShiftL ty) [x, y] =
    SexprList [ sinterStdlib "shiftl", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (ShiftR ty) [x, y] =
    SexprList [ sinterStdlib "shiftr", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (BAnd ty) [x, y] =
    SexprList [ sinterStdlib "bitwAnd", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (BOr ty) [x, y] =
    SexprList [ sinterStdlib "bitwOr", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (BXOr ty) [x, y] =
    SexprList [ sinterStdlib "bitwXor", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (LT ty) [x, y] =
    SexprList [ sinterStdlib "lt", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (LTE ty) [x, y] =
    SexprList [ sinterStdlib "lte", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (EQ ty) [x, y] =
    SexprList [ sinterStdlib "eq", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (GTE ty) [x, y] =
    SexprList [ sinterStdlib "gte", aVarToSexpr x, aVarToSexpr y ]

  primFnToSexpr (GT ty) [x, y] =
    SexprList [ sinterStdlib "gt", aVarToSexpr x, aVarToSexpr y ]

  -- TODO
  primFnToSexpr StrLength [s] = ?sinterStrLen
  primFnToSexpr StrHead [s] = ?sinterStrHead
  primFnToSexpr StrTail [s] = ?sinterStrTail
  primFnToSexpr StrIndex [s, i] = ?sinterStrIndex
  primFnToSexpr StrCons [s1, s2] = ?sinterStrCons
  primFnToSexpr StrAppend [s1, s2] =
    SexprList [ sinterStdlib "strAppend", aVarToSexpr s1, aVarToSexpr s2 ]
  primFnToSexpr StrReverse [s] = ?sinterStrReverse
  primFnToSexpr StrSubstr [i, j, s] = ?sinterSubstr

  -- TODO
  primFnToSexpr DoubleExp [d] = ?primFnToSexpr_rhs_25
  primFnToSexpr DoubleLog [d] = ?primFnToSexpr_rhs_26
  primFnToSexpr DoubleSin [d] = ?primFnToSexpr_rhs_27
  primFnToSexpr DoubleCos [d] = ?primFnToSexpr_rhs_28
  primFnToSexpr DoubleTan [d] = ?primFnToSexpr_rhs_29
  primFnToSexpr DoubleASin [d] = ?primFnToSexpr_rhs_30
  primFnToSexpr DoubleACos [d] = ?primFnToSexpr_rhs_31
  primFnToSexpr DoubleATan [d] = ?primFnToSexpr_rhs_32
  primFnToSexpr DoubleSqrt [d] = ?primFnToSexpr_rhs_33
  primFnToSexpr DoubleFloor [d] = ?primFnToSexpr_rhs_34
  primFnToSexpr DoubleCeiling [d] = ?primFnToSexpr_rhs_35

  -- TODO
  primFnToSexpr (Cast x y) [z] = ?primFnToSexpr_rhs_36
  primFnToSexpr BelieveMe [_, _, thing] = aVarToSexpr thing
                                        -- ^ I believe this is correct?

  primFnToSexpr Crash [fc, reason] =
    sinterCrash



  ||| Create a call to a function which evaluates `in` over `let`
  |||   let f x = y in z
  ||| is equivalent to
  |||   (\f . z) (\x . y)
  aLetToSexpr : FC -> (var : Int) -> (val : ANF) -> (in_expr : ANF) -> Sexpr
  aLetToSexpr fc var val in_expr =
    let
      varName = intNameToSinterID var
      cFunName = MkSinterID $ ">>let_" ++ ("a" ++ show var) ++ "_<<in_" ++ show fc
      val_sexpr = anfToSexpr val
      in_sexpr = anfToSexpr in_expr
      --cFunDef = SinDef $ cFunName val_sexpr
    in
      ?aLetToSexpr_rhs

  anfToSexpr : ANF -> Sexpr
  anfToSexpr (AV fc x) =
    aVarToSexpr x

  anfToSexpr (AAppName fc _ n fArgs) =
      let
        funName = SexprID $ mangle n
        funArgs = map aVarToSexpr fArgs
      in
        SexprList $ funName :: funArgs

  anfToSexpr (AUnderApp fc n missing partArgs) =
      let
        sinName  = SexprID $ mangle n
        sinMiss  = SexprLit $ SinInt (cast missing) nArgsWidth
        nArgs    = length partArgs
        sinNArgs = SexprLit $ SinInt (cast nArgs) nArgsWidth
        -- number of args function expects
        sinArity = SexprLit $ SinInt (cast (missing + nArgs)) nArgsWidth
        -- list of arguments
        sinArgs  = SexprList $ map aVarToSexpr partArgs
      in
        -- make a closure containing the above info (sinter-specific closure)
        SexprList [sinterClosureCon , sinName , sinArity , sinNArgs , sinArgs]


  -- application of a closure to another argument; potentially to the last arg
  anfToSexpr (AApp fc _ closure arg) =
    let
      sinClosure = aVarToSexpr closure
      sinArg = aVarToSexpr arg
    in
      SexprList [sinterClosureAdd, sinClosure, sinArg]


  anfToSexpr (ALet fc var let_expr in_expr) =
    aLetToSexpr fc var let_expr in_expr

  anfToSexpr (ACon fc n tag xs) =
    let
      (MkSinterID mn) = mangle n
      name = MkSinterID $ mn ++ show tag
      fArgs = map aVarToSexpr xs
    in
      SexprList $ (SexprID name) :: fArgs

  anfToSexpr (AOp fc _ fn args) = primFnToSexpr fn args

  anfToSexpr (AExtPrim fc _ n args) = ?anfToSexpr_rhs_8

  anfToSexpr (AConCase fc avar alts m_default) = ?anfToSexpr_rhs_9

  anfToSexpr (AConstCase fc x xs y) = ?anfToSexpr_rhs_10

  anfToSexpr (APrimVal fc c) = constantToSexpr c

  anfToSexpr (AErased fc) =
    SexprLit $ SinInt 0 0

  anfToSexpr (ACrash fc x) =
    sinterCrash

compileANF : (Name, ANFDef) -> Core SinterGlobal
compileANF (n, (MkAFun args body)) =
  let
    sinName = mangle n
    sinArgs = map intNameToSinterID args
    sinBody = anfToSexpr body
  in
    pure $ SinDef sinName sinArgs sinBody
compileANF (n, (MkACon tag arity def)) = ?compileANF_rhs_3
compileANF (n, (MkAForeign ccs fargs x)) = ?compileANF_rhs_4
compileANF (n, (MkAError e)) = ?compileANF_rhs_5

----------------
-- TOP OF API --
----------------

compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
        ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile context tmpDir outputDir term outfile =
  do compData <- getCompileData False ANF term
     let defs = anf compData
     sinterGlobs <- traverse compileANF defs
     -- readyForCG <- traverse bubbleLets sinterGlobs
     ?compile_rhs

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute context tmpDir term =
  throw $ InternalError "Sinter backend can only compile, sorry."

sinterCodegen : Codegen
sinterCodegen = MkCG compile execute

main : IO ()
main = mainWithCodegens [("sinter", sinterCodegen)]

