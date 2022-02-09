-- vim: tw=80 sw=2 ts=2 et

module Idris2Sinter

import Compiler.Common -- for getCompileData
import Compiler.LambdaLift -- for Lifted
import Core.Context
import Core.CompileExpr
import Data.List -- for head
import Data.Vect
import Data.String.Extra -- for join
import Idris.Driver -- for mainWithCodegens

import Sinter

{- FIXME
 - 
 - simpleTPF, defined below, would like to use Data.Vect.(::), however
 - un-%hiding it gives a bunch of "Ambiguous elaboration" errors in places
 - where SinterList is used. This is likely because SinterList can accept
 - not just Lists, but any type that implements Foldable and Functor---I
 - implemented it this way so that Vects and similar would not have to be
 - converted into Lists to be used, but now we're using toList in simpleTPF
 - anyway!
 -}
%hide Data.Vect.(::)
%hide Core.TT.CList.(::)

%hide Core.CompileExpr.SubstCEnv.(::)
%hide Core.TT.SubstEnv.(::)
%hide Prelude.Stream.(::)

todo : String -> List SinterID
todo x = [ MkSinterID x ]

mangleNS : Namespace -> String
mangleNS = showNSWithSep "::"

simpleMangle : List String -> String
simpleMangle = join "_"

mangle : Name -> String
mangle (NS ns name) =
  let
    ns' = mangleNS ns
    name' = mangle name
  in ns' ++ "::" ++ name'

mangle (UN x) = show x
mangle (MN x i) = x ++ "-" ++ (show i)
mangle (PV n i) = mangle n ++ "-" ++ (show i)
mangle (DN _ y) = mangle y
mangle (Nested (i, j) n) = simpleMangle [ "nested", show i, show j, mangle n ]
mangle (CaseBlock   x i) = simpleMangle [ "case", x, show i ]
mangle (WithBlock   x i) = simpleMangle [ "with", x, show i ]
mangle (Resolved      i) = simpleMangle [ "resolved", show i ]

mangleToSinterID : Name -> SinterID
mangleToSinterID = MkSinterID . mangle

mangleToSinterExpr : Name -> SinterExpr
mangleToSinterExpr = SinterExprID . mangleToSinterID

constInt : Int -> Nat -> SinterExpr
constInt x w = SinterLiteralExpr $ SinterInt x w

constStr : String -> SinterExpr
constStr = SinterLiteralExpr . SinterStr

translateConstant : Constant -> SinterExpr
translateConstant c = case c of

  I   x => constInt (cast x) 64
  I8  x => constInt (cast x) 8
  I16 x => constInt (cast x) 16
  I32 x => constInt (cast x) 32
  I64 x => constInt (cast x) 64

  BI  x => constInt (cast x) 64
  B8  x => constInt (cast x) 8
  B16 x => constInt (cast x) 16
  B32 x => constInt (cast x) 32
  B64 x => constInt (cast x) 64

  Str x => constStr x
  Ch  x => constInt (cast x) 64
  Db  x => ?constantToSexpr_rhs_9

  WorldVal => SinterExprID $ MkSinterID "WORLD"
  IntType => ?constantToSexpr_rhs_11
  Int8Type => ?fhaconstantToSexpr_rhs_13
  Int16Type => ?cdahfuoonstantToSexpr_rhs_14
  Int32Type => ?constafeuhasntToSexpr_rhs_15
  Int64Type => ?constantToSfhsexpr_rhs_16
  IntegerType => ?constantToSexpr_rhs_12
  Bits8Type => ?constantToSexpr_rhs_13
  Bits16Type => ?constantToSexpr_rhs_14
  Bits32Type => ?constantToSexpr_rhs_15
  Bits64Type => ?constantToSexpr_rhs_16
  StringType => ?constantToSexpr_rhs_17
  CharType => ?constantToSexpr_rhs_18
  DoubleType => ?constantToSexpr_rhs_19
  WorldType => ?constantToSexpr_rhs_20

-- TODO
sinterPrimFn : String -> SinterExpr
sinterPrimFn = SinterExprID . MkSinterID

sinterNum : Nat -> SinterExpr
sinterNum i = SinterLiteralExpr $ SinterInt (cast i) 32

sinterID : String -> SinterExpr
sinterID = SinterExprID . MkSinterID

-- Forward declaration; definition below.
transExpr : {vars : _} -> Lifted vars -> SinterExpr

simpleTPF : {vars : _} -> String -> Vect a (Lifted vars) -> SinterExpr
simpleTPF fn args
  = SinterList $ sinterPrimFn fn :: toList (map transExpr args)

transPrimFn : {vars : _} -> PrimFn a -> Vect a (Lifted vars) -> SinterExpr
transPrimFn = simpleTPF . show

transLet : {vars : _} -> (x : Name) -> Lifted vars -> Lifted (x::vars) -> SinterExpr
transLet new old in_expr =
  let
    let' = sinterID "let"
    new' = mangleToSinterExpr new
    old' = transExpr old
    in_expr' = transExpr in_expr
  in
    SinterList [ let', SinterPair (new', old'), in_expr' ]

transLConAlt : {vars : _} -> SinterExpr -> LiftedConAlt vars -> SinterExpr
transLConAlt n (MkLConAlt cname _ tag args expr) =
  let
    match : SinterExpr
    match = constInt (maybe 0 id tag) 32 -- FIXME hardcoded width
    expr' : SinterExpr
    expr' =
      let
        lets : Name -> Nat -> (SinterExpr, SinterExpr)
        lets a i = (mangleToSinterExpr a,
                   SinterList [ sinterID $ mangle cname ++ ".member-" ++ show i
                              , n
                              ]
                   )
        letIns : List (SinterExpr, SinterExpr)
        letIns = zipWith lets args [1..(length args)]
        lh : (SinterExpr, SinterExpr) -> SinterExpr -> SinterExpr
        lh l expr = SinterList [ sinterID "let", SinterPair l, expr ]
      in
        foldr lh (transExpr expr) letIns
  in
    SinterPair (match, expr')

transLocal : {vars : _} -> {idx : _} -> (0 p : IsVar _ idx vars) -> SinterExpr
transLocal p =
  let
    ivmib : (k : Nat) -> (ns : List Name) -> IsVar n k ns -> InBounds k ns
    ivmib Z _ First = InFirst
    ivmib (S i) (_::xs) (Later p) = InLater (ivmib i xs p)
  in
    mangleToSinterExpr $ index idx vars {ok = (ivmib idx vars p)}

-- Complete function application
transAppName : {vars : _} -> Name -> List (Lifted vars) -> SinterExpr
transAppName n args =
  let
    n' = mangleToSinterExpr n
  in
    SinterList (n' :: map transExpr args)

||| Create a closure.
closure : Name -> Nat -> SinterExpr
closure fname arity = SinterList [ sinterID "closure"
                                 , mangleToSinterExpr fname
                                 , sinterNum arity
                                 ]

||| Apply an argument to a closure.
app : SinterExpr -> SinterExpr -> SinterExpr
app c x = SinterList [ sinterID "closureApp", c, x ]

||| Apply several arguments to a closure at once.
-- it's foldr!
apps : SinterExpr -> List SinterExpr -> SinterExpr
apps c      [] = c
apps c (x::xs) = apps (app c x) xs

-- partial function application
transUnderApp : {vars : _} -> Name -> Nat -> List (Lifted vars) -> SinterExpr
transUnderApp fname unprovidedArgc args =
  let
    arity = unprovidedArgc + (length args)
    c = closure fname arity
    args' : List SinterExpr
    args' = map transExpr args
  in
    apps c args'

-- closure application (potentially complete)
transApp : {vars : _} -> Lifted vars -> Lifted vars -> SinterExpr
transApp closure arg =
  SinterList [ sinterID "closureApp"
             , transExpr closure
             , transExpr arg
             ]

-- Constructor
transCon : {vars : _} -> Name -> ConInfo -> List (Lifted vars) -> SinterExpr
transCon name tag args = 
  let
    name' = sinterID (mangle name)
    -- Not sure why the type declaration is needed here
    args' : List SinterExpr
    args' = map transExpr args
  in
    SinterList (name'::args')

transConstAlt : {vars : _} -> LiftedConstAlt vars -> SinterExpr
transConstAlt (MkLConstAlt match expr) = SinterPair (translateConstant match,
                                                     transExpr expr
                                                     )

transConstCase : {vars : _} -> Lifted vars -> List (LiftedConstAlt vars) ->
                 Maybe (Lifted vars) -> SinterExpr
transConstCase expr alts mdef =
  SinterList [ sinterID "case"
             , transExpr expr
             , SinterList $ map transConstAlt alts
             , maybe (SinterList [ sinterID "sinter_crash" ]) transExpr mdef
             ]

transConCase : {vars : _} -> Lifted vars -> List (LiftedConAlt vars) ->
               Maybe (Lifted vars) -> SinterExpr
transConCase expr alts mdef =
  let
    expr' = transExpr expr
    -- cname = mangle $ case head alts of MkLConAlt n _ _ _ _ => n
    cname = "dummy"
    unique = sinterID "UNIQUE"
    caseStmt : SinterExpr -> SinterExpr
    caseStmt x =
      SinterList [ sinterID "case"
                 , SinterList [ sinterID (cname ++ ".tag")
                              , x
                              ]
                 , SinterList $ map (transLConAlt x) alts
                 , maybe (SinterList [ sinterID "sinter_crash" ]) transExpr mdef
                 ]
  in
    case expr' of
         SinterExprID _ => caseStmt expr'
         _ => SinterList [ sinterID "let"
                         , SinterPair (unique, expr')
                         , caseStmt unique
                         ]

-- transConCase expr alts mdef =
--   let
--     letName = "UNIQUE" -- FIXME not actually unique yet
--     letName' = sinterID letName
--     wrapper = \e => SinterList [ sinterID "let"
--                                , SinterPair (letName', transExpr expr)
--                                , e
--                                ]
--   in
--     wrapper (SinterList [ sinterID "case"
--                         , sinterID (letName ++ ".tag")
--                         , SinterList $ map (transLConAlt letName) alts
--                         , maybe (sinterID "sinter_crash") transExpr mdef
--                         ])

-- As declared above:
-- transExpr : {vars : _} -> Lifted vars -> SinterExpr
transExpr (LLocal _ p) = transLocal p
transExpr (LAppName _ _ n args) = transAppName n args
transExpr (LUnderApp _ n m args) = transUnderApp n m args
transExpr (LApp _ _ c arg) = transApp c arg
transExpr (LCon _ n tag _ xs) = transCon n tag xs
transExpr (LOp _ _ x xs) = transPrimFn x xs
transExpr (LConstCase _ expr alts mdef) = transConstCase expr alts mdef
transExpr (LLet _ n existing in_expr) = transLet n existing in_expr
transExpr (LPrimVal _ x) = translateConstant x
transExpr (LErased _) = SinterLiteralExpr $ SinterInt 0 1
transExpr (LConCase _ x xs y) = transConCase x xs y
transExpr (LCrash _ _) = sinterID "TODO_LCrash"
transExpr (LExtPrim _ _ p xs) = sinterID "TODO_LExtPrim"

transDef : (Name, LiftedDef) -> Core SinterTopLevel
transDef (n, d) = pure $ case d of

  MkLFun args scope body =>
    let
      n' = mangleToSinterID n
      args' = map mangleToSinterID (args ++ scope)
      body' = transExpr body
    in
      SinterDef n' args' body'

  MkLCon tag arity nt =>
    let
      n' = mangleToSinterID n
      mems = map (\x => "member-" ++ show x) [1..arity]
      mems' = case tag of
                   Just _ => "tag"::mems
                   Nothing => mems
    in
      SinterType n' (map MkSinterID mems')

  MkLForeign ccs args x =>
    let
      n' = mangleToSinterID n
      args' = zipWith (\x, y => show x ++ show y) args [1..(length args)]
    in
      SinterDec n' (map MkSinterID args')

  MkLError x => SinterDec (mangleToSinterID n) []

compile : Ref Ctxt Defs -> String -> String -> ClosedTerm -> String
        -> Core (Maybe String)
compile ctxt tmp out term outfile = do
  cd <- getCompileData False Lifted term
  let defs = lambdaLifted cd
  sinterGlobs <- traverse transDef defs
  coreLift $ putStrLn (gen sinterGlobs)
  pure $ Nothing

execute : Ref Ctxt Defs -> String -> ClosedTerm -> Core ()
execute _ _ _ = ?execution

sinterCodegen : Codegen
sinterCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("sinter", sinterCodegen)]
