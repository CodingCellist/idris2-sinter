-- vim: tw=80 sw=2 ts=2 et

module Idris2Sinter

import Compiler.Common -- for getCompileData
import Compiler.LambdaLift -- for Lifted
import Core.Context
import Core.CompileExpr
import Data.List -- for head
import Data.List1
import Data.Vect
import Data.String
import Data.String.Extra -- for join
import Idris.Driver -- for mainWithCodegens
import Libraries.Utils.Path

import Idris.Syntax

import Sinter
import TagList

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
mangleToSinterID = MkSinterID . sanitise . mangle
  where
    disallowed : Char -> Bool
    disallowed '{' = True
    disallowed '}' = True
    disallowed '(' = True
    disallowed ')' = True
    disallowed '$' = True
    disallowed _ = False

    sanitise : String -> String
    sanitise s = let s = concat $ split disallowed s
                 in join "^" $ words s

mangleToSinterExpr : Name -> SinterExpr
mangleToSinterExpr = SinterExprID . mangleToSinterID

constInt : Int -> Nat -> SinterExpr
constInt x w = SinterLiteralExpr $ SinterInt x w

constStr : String -> SinterExpr
constStr = SinterLiteralExpr . SinterStr

translatePrimType : PrimType -> SinterExpr
translatePrimType IntType = ?translatePrimType_rhs_0
translatePrimType Int8Type = ?translatePrimType_rhs_1
translatePrimType Int16Type = ?translatePrimType_rhs_2
translatePrimType Int32Type = ?translatePrimType_rhs_3
translatePrimType Int64Type = ?translatePrimType_rhs_4
translatePrimType IntegerType = ?translatePrimType_rhs_5
translatePrimType Bits8Type = ?translatePrimType_rhs_6
translatePrimType Bits16Type = ?translatePrimType_rhs_7
translatePrimType Bits32Type = ?translatePrimType_rhs_8
translatePrimType Bits64Type = ?translatePrimType_rhs_9
translatePrimType StringType = ?translatePrimType_rhs_10
translatePrimType CharType = ?translatePrimType_rhs_11
translatePrimType DoubleType = ?translatePrimType_rhs_12
translatePrimType WorldType = ?translatePrimType_rhs_13

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
  PrT x => translatePrimType x

  WorldVal => constInt 0 8

-- TODO
sinterPrimFn : String -> SinterExpr
sinterPrimFn = SinterExprID . MkSinterID

sinterNum : Nat -> SinterExpr
sinterNum i = SinterLiteralExpr $ SinterInt (cast i) 32

sinterID : String -> SinterExpr
sinterID = SinterExprID . MkSinterID

-- Forward declaration; definition below.
transExpr : {vars : _} -> TagList -> Lifted vars -> (SinterExpr, TagList)

tmap : (TagList -> a -> (b, TagList)) -> List a -> TagList -> (List b, TagList)
tmap f [] tl = ([], tl)
tmap f (x :: xs) tl =
  let
    (sin, tl') = f tl x
    (sins, tls) = tmap f xs tl'
  in
    (sin :: sins, tls)

simpleTPF : {vars : _} -> TagList -> String -> Vect a (Lifted vars) ->
            (SinterExpr, TagList)
simpleTPF tags fn args =
  let
    (sins, tags') = tmap transExpr (toList args) tags
  in
    (SinterList $ sinterPrimFn fn :: sins, tags')

transPrimFn : {vars : _} -> TagList -> PrimFn a -> Vect a (Lifted vars) ->
              (SinterExpr, TagList)
transPrimFn tags = (simpleTPF tags) . show

transLet : {vars : _} -> TagList -> (x : Name) -> Lifted vars ->
           Lifted (x :: vars) -> (SinterExpr, TagList)
transLet tags new old in_expr =
  let
    let' = sinterID "let"
    new' = mangleToSinterExpr new
    (old', tags) = transExpr tags old
    (in_expr', tags) = transExpr tags in_expr
  in
    (SinterList [ let', SinterPair (new', old'), in_expr' ], tags)

transLConAlt : {vars : _} -> SinterExpr -> TagList -> LiftedConAlt vars ->
               (SinterExpr, TagList)
transLConAlt n tags (MkLConAlt cname _ tag args expr) =
  let
    (i, tags') = find' cname tags
    match = constInt (cast i) 64 -- TODO fixed match width
    lets : Name -> Nat -> (SinterExpr, SinterExpr)
    lets a i = (mangleToSinterExpr a,
               SinterList [ sinterID $ "dummy" ++ ".member-" ++ show i
                          , n
                          ]
               )
    letIns : List (SinterExpr, SinterExpr)
    letIns = zipWith lets args [1..(length args)]
    lh : (SinterExpr, SinterExpr) -> SinterExpr -> SinterExpr
    lh l expr = SinterList [ sinterID "let", SinterPair l, expr ]
    acc' : (SinterExpr, TagList)
    acc' = transExpr tags' expr
    acc : SinterExpr
    acc = fst acc'
    tags'' : TagList
    tags'' = snd acc'
    expr' : SinterExpr
    expr' = foldr lh acc letIns
  in
    (SinterPair (match, expr'), tags'')

transLocal : {vars : _} -> {idx : _} -> (0 p : IsVar _ idx vars) -> SinterExpr
transLocal p =
  let
    ivmib : (k : Nat) -> (ns : List Name) -> IsVar n k ns -> InBounds k ns
    ivmib Z _ First = InFirst
    ivmib (S i) (_::xs) (Later p) = InLater (ivmib i xs p)
  in
    mangleToSinterExpr $ index idx vars {ok = (ivmib idx vars p)}

-- Complete function application
transAppName : {vars : _} -> TagList -> Name -> List (Lifted vars) ->
               (SinterExpr, TagList)
transAppName tags n args =
  let
    n' = mangleToSinterExpr n
    (args, tags) = tmap transExpr args tags
  in
    (SinterList (n' :: args), tags)

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
transUnderApp : {vars : _} -> TagList -> Name -> Nat -> List (Lifted vars) ->
                (SinterExpr, TagList)
transUnderApp tags fname unprovidedArgc args =
  let
    arity = unprovidedArgc + (length args)
    c = closure fname arity
    (args', tags) = tmap transExpr args tags
  in
    (apps c args', tags)

-- closure application (potentially complete)
transApp : {vars : _} -> TagList -> Lifted vars -> Lifted vars ->
           (SinterExpr, TagList)
transApp tags closure arg =
  let
    (closure', tags) = transExpr tags closure
    (arg', tags) = transExpr tags arg
  in
    ( SinterList [ sinterID "closureApp"
                 , closure'
                 , arg'
                 ]
    , tags
    )

-- constructor call
transCon : {vars : _} -> TagList -> Name -> ConInfo -> List (Lifted vars) ->
           (SinterExpr, TagList)
transCon tags name ci args = 
  let
    name' = sinterID (mangle name)
    -- the first argument here is the tag given to the object
    -- to check its ADT type when case splitting it
    (tag, tags) = find' name tags
    (tail, tags) = tmap transExpr args tags
    tag = constInt (cast tag) 64 -- TODO fixed tag width
    args' = tag :: tail
  in
    (SinterList (name' :: args'), tags)

transConstAlt : {vars : _} -> TagList -> LiftedConstAlt vars ->
                (SinterExpr, TagList)
transConstAlt tags (MkLConstAlt match expr) =
  let
    (expr', tags) = transExpr tags expr
  in
    ( SinterPair (translateConstant match, expr')
    , tags
    )

transIntConstCase : {vars : _} -> TagList -> Lifted vars ->
                    List (LiftedConstAlt vars) -> Maybe (Lifted vars) ->
                    (SinterExpr, TagList)
transIntConstCase tags expr alts mdef =
  let
    emptyElse = SinterList [ sinterID "sinter_crash" ]
    (expr', tags) = transExpr tags expr
    (mdef', tags) = maybe (emptyElse, tags) (transExpr tags) mdef
    (alts', tags) = tmap transConstAlt alts tags
  in
    (SinterList [ sinterID "case", expr', SinterList alts', mdef' ], tags)

transStringConstCase : {vars : _} -> TagList -> Lifted vars ->
                       List (LiftedConstAlt vars) -> Maybe (Lifted vars) ->
                       (SinterExpr, TagList)
transStringConstCase tags expr [] mdef =
  case mdef of
       Nothing  => (SinterList [ sinterID "sinter_crash" ], tags)
       Just def => transExpr tags def
-- [if [eq a b] [then_body] [else_body] eqw]
transStringConstCase tags expr ((MkLConstAlt match then') :: alts) mdef =
  let
    match = translateConstant match
    (expr', tags) = transExpr tags expr
    (then', tags) = transExpr tags then'
    (else', tags) = transStringConstCase tags expr alts mdef
    eqWidth = SinterIfWidth 64
    eqf = SinterList [ sinterID "sinter_str_eq"
                     , match
                     , expr'
                     ]
  in
    ( SinterList [ sinterID "if"
                 , eqf
                 , then'
                 , else'
                 , eqWidth
                 ]
    , tags
    )

data CaseType = IntLike | StringLike | WeirdLike | NoAlts

caseType : List (LiftedConstAlt vars) -> CaseType
caseType [] = NoAlts
caseType ((MkLConstAlt m e) :: alts) =
  case m of
       I   _ => IntLike
       I8  _ => IntLike
       I16 _ => IntLike
       I32 _ => IntLike
       I64 _ => IntLike

       Str _ => StringLike

       BI  _ => WeirdLike
       B8  _ => WeirdLike
       B16 _ => WeirdLike
       B32 _ => WeirdLike
       B64 _ => WeirdLike

       Ch  _ => WeirdLike
       Db  _ => WeirdLike
       PrT _ => WeirdLike

       WorldVal => WeirdLike

transConstCase : {vars : _} -> TagList -> Lifted vars ->
                 List (LiftedConstAlt vars) -> Maybe (Lifted vars) ->
                 (SinterExpr, TagList)
transConstCase tags expr alts mdef =
  case caseType alts of
       IntLike => transIntConstCase tags expr alts mdef
       StringLike => transStringConstCase tags expr alts mdef
       WeirdLike => ?weirdConstCase tags expr alts mdef
       NoAlts => ?emptyConstCase tags expr alts mdef

transLConAlts : {vars : _} -> String -> List (LiftedConAlt vars) -> TagList ->
                (List SinterExpr, TagList)
transLConAlts n xs tags = tmap (transLConAlt (sinterID n)) xs tags

sinterLet : (new : String) -> (old : SinterExpr) -> (body : SinterExpr) ->
            SinterExpr
sinterLet new old body = SinterList [ sinterID "let"
                                    , SinterPair (sinterID new, old)
                                    , body
                                    ]

transConCase : {vars : _} -> TagList -> Lifted vars ->
               List (LiftedConAlt vars) -> Maybe (Lifted vars)
               -> (SinterExpr, TagList)
transConCase tags expr alts mdef =
  let
    (expr', tags) = transExpr tags expr
    -- cname = mangle $ case head alts of MkLConAlt n _ _ _ _ => n
    cname = "dummy"
    unique = "UNIQUE"
    (alts', tags) = transLConAlts unique alts tags
    m = SinterList [ sinterID "sinter_crash" ]
    (mdef', tags) = maybe (m, tags) (transExpr tags) mdef
    caseStmt : SinterExpr
    caseStmt =
      SinterList [ sinterID "case"
                 , SinterList [ sinterID (cname ++ ".tag")
                              , sinterID unique
                              ]
                 , SinterList alts'
                 , mdef'
                 ]
  in
    (sinterLet unique expr' caseStmt, tags)

-- As declared above:
-- transExpr : {vars : _} -> Lifted vars -> SinterExpr
transExpr tags (LLocal _ p) = (transLocal p, tags)
transExpr tags (LAppName _ _ n args) = transAppName tags n args
transExpr tags (LUnderApp _ n m args) = transUnderApp tags n m args
transExpr tags (LApp _ _ c arg) = transApp tags c arg
transExpr tags (LCon _ n tag _ xs) = transCon tags n tag xs
transExpr tags (LOp _ _ x xs) = transPrimFn tags x xs
transExpr tags (LConstCase _ expr alts mdef) =
  transConstCase tags expr alts mdef
transExpr tags (LLet _ n existing in_expr) = transLet tags n existing in_expr
transExpr tags (LPrimVal _ x) = (translateConstant x, tags)
transExpr tags (LErased _) = (SinterLiteralExpr $ SinterInt 0 1, tags)
transExpr tags (LConCase _ x xs y) = transConCase tags x xs y
transExpr tags (LCrash _ _) = (sinterID "TODO_LCrash", tags)
transExpr tags (LExtPrim _ _ p xs) = (sinterID "TODO_LExtPrim", tags)

transDef : TagList -> (Name, LiftedDef) -> (SinterTopLevel, TagList)
transDef tags (n, d) = case d of

  MkLFun args scope body =>
    let
      n' = mangleToSinterID n
      args' = map mangleToSinterID (args ++ reverse scope)
      (body', tags) = transExpr tags body
    in
      (SinterDef n' args' body', tags)

  MkLCon tag arity nt =>
    let
      n' = mangleToSinterID n
      mems = map (\x => "member-" ++ show x)
        (if arity == 0 then [] else [1..arity])
      mems' = case tag of
                   Just i => ("tag" ++ show i) :: mems
                   -- Just _ => mems
                   Nothing => mems
    in
      (SinterType n' (map MkSinterID mems'), tags)

  MkLForeign ccs args x =>
    let
      n' = mangleToSinterID n
      args' = zipWith (\x, y => show x ++ show y) args [1..(length args)]
    in
      (SinterDec n' (map MkSinterID args'), tags)

  MkLError x => (SinterDec (mangleToSinterID n) [], tags)

dec : String -> List String -> SinterTopLevel
dec n args = SinterDec (MkSinterID n) (map MkSinterID args)

type : String -> List String -> SinterTopLevel
type n members = SinterType (MkSinterID n) (map MkSinterID members)

runtimeDecs : List SinterTopLevel
runtimeDecs = [
  dec "closureApp" ["c", "arg"],
  dec "closure" ["f", "arity"],
  dec "sinter_crash" [],
  dec "++" ["a", "b"],
  dec "believe_me" ["a", "b", "x"],
  dec "sinter_str_eq" ["a", "b"],

  dec "cast-Integer-String" ["a"],

  dec "op_strhead" ["str"],
  dec "op_strtail" ["str"],
  dec "op_strindex" ["str", "n"],

  type "dummy" ("tag" :: map (("member-" ++) . show) [1..32])

  ] ++ [dec (y ++ x) ["a", "b"] |
          x <- ["Integer", "Char"],
          y <- ["+", "-", "*", "/", "<", "<=", "==", ">=", ">"]]

mfilter : List (Maybe a) -> List a
mfilter [] = []
mfilter (Nothing :: xs) = mfilter xs
mfilter (Just x :: xs) = x :: mfilter xs

mmap : (a -> Maybe b) -> List a -> List b
mmap f xs = mfilter $ map f xs

decOfDef : SinterTopLevel -> Maybe SinterTopLevel
decOfDef (SinterDef n args _) = Just $ SinterDec n args
decOfDef _ = Nothing

redundantDecs : List SinterTopLevel -> List SinterTopLevel
redundantDecs = mmap decOfDef

trans : List (Name, LiftedDef) -> List SinterTopLevel
trans xs =
  let (defs, _) = tmap transDef xs []
  in  defs ++ runtimeDecs ++ redundantDecs defs

covering
Eq SinterTopLevel where
  (==) (SinterDef _ _ _) (SinterDef _ _ _) = True
  (==) (SinterDec _ _) (SinterDec _ _) = True
  (==) (SinterType _ _) (SinterType _ _) = True
  (==) _ _ = False

covering
Ord SinterTopLevel where
  compare (SinterDef _ _ _) (SinterDef _ _ _) = EQ
  compare (SinterDef _ _ _) (SinterDec _ _) = LT
  compare (SinterDef _ _ _) (SinterType _ _) = LT

  compare (SinterDec _ _) (SinterDef _ _ _) = GT
  compare (SinterDec _ _) (SinterDec _ _) = EQ
  compare (SinterDec _ _) (SinterType _ _) = LT

  compare (SinterType _ _) (SinterDef _ _ _) = GT
  compare (SinterType _ _) (SinterDec _ _) = GT
  compare (SinterType _ _) (SinterType _ _) = EQ

compile : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String ->
          ClosedTerm -> String -> Core (Maybe String)
compile ctxt syn tmp out term outfile = do
  cd <- getCompileData False Lifted term
  let defs = lambdaLifted cd
  let sinterGlobs = sort $ trans defs
  let output = out </> outfile
  writeFile output (gen sinterGlobs)
  pure (Just output)

execute : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm ->
          Core ()
execute _ _ _ _ = coreFail (UserError
                           "this backend cannot execute, only compile")

sinterCodegen : Codegen
sinterCodegen = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("sinter", sinterCodegen)]
