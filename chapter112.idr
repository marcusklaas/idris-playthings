module Main

import Data.Primitives.Views
import System

data InfIO : Type where
     Do : IO a
          -> (a -> Inf InfIO)
          -> InfIO

total
loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg)
                   (\_ => loopPrint msg)

total
run : InfIO -> IO ()
run (Do action continuation)
  = do value <- action
       run $ continuation value

data Fuel = Dry | More Fuel

total
tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More $ tank k

total
runWithFuel : Fuel -> InfIO -> IO ()
runWithFuel (More fuel) (Do val cont) = do res <- val
                                           runWithFuel fuel (cont res)
runWithFuel Dry p = putStrLn "Ran out of fuel"

data SuperFuel = NoMore | MoreFuel (Lazy SuperFuel)

forever : SuperFuel
forever = MoreFuel forever


total
runWithSuperFuel : SuperFuel -> InfIO -> IO ()
runWithSuperFuel NoMore _ = putStrLn "Ran out of superfuel!"
runWithSuperFuel (MoreFuel f) (Do action cont)
    = do res <- action
         runWithSuperFuel f (cont res)

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

total
loopPrintTwo : String -> InfIO
loopPrintTwo msg = do putStrLn msg
                      loopPrintTwo msg

total
quiz : Stream Int -> (score : Nat) -> InfIO
quiz (num1 :: num2 :: rest) score
  = do putStrLn ("Score so far: " ++ show score)
       putStr (show num1 ++ " * " ++ show num2 ++ " = ")
       answer <- getLine
       if (cast answer == num1 * num2)
          then do putStrLn "Correct!"
                  quiz rest (S score)
          else do putStrLn $ "Wrong, the answer is " ++ (show $ num1 * num2)
                  quiz rest score

total
randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

total
arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

partial
main : IO ()
main = do seed <- time
          runWithSuperFuel forever $ quiz (arithInputs $ fromInteger seed) Z

total
totalRepl : (prompt : String) -> (action : String -> String) -> InfIO
totalRepl prompt action
  = do putStr prompt
       map action getLine >>= putStrLn
       totalRepl prompt action
