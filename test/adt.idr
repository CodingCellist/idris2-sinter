data ADT = Left Integer | Right String

showADT : ADT -> String
showADT (Left i) = show i
showADT (Right s) = s

Show ADT where
  show = showADT

main : IO ()
main = putStrLn (show $ Left 4)
