module Main

%foreign "sinter:prim__puts"
prim__puts : String -> PrimIO ()

||| Output a string to stdout without a trailing newline.
export
putStr : HasIO io => String -> io ()
putStr str = primIO (prim__puts str)

main : IO ()
main = Main.putStr "Hello sinter world!"
