-- Idris2

module Sinter

import Core.Context
import Compiler.Common
import Idris.Driver

compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
        ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs tmpDir outputDir y outfile = ?compile_rhs

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute defs tmpDir y = ?execute_rhs

sinterCodegen : Codegen
sinterCodegen = MkCG compile execute

main : IO ()
main = mainWithCodegens [("sinter", sinterCodegen)]


