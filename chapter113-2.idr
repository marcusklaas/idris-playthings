module Main

import System
import Data.Primitives.Views

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile : (String, String) -> Command (Either FileError ())

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

total
runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do res <- runCommand x
                           runCommand (f res)
runCommand (ReadFile fn) = readFile fn
runCommand (WriteFile (fn, contents)) = writeFile fn contents

total
run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry cons = pure Nothing
run (More _) (Quit x) = (pure . Just) x
run (More f) (Do action cont) = do res <- runCommand action
                                   run f $ cont res

quitString : String
quitString = "quit"

data Input = Answer Int
           | QuitCmd

total
readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == quitString
                        then Pure QuitCmd
                        else Pure (Answer (cast answer))

record Score where
  constructor MkScore
  correctCount, wrongCount : Int

rightAnswer : Score -> Score
rightAnswer score = record { correctCount $= (+ 1 ) } score

wrongAnswer : Score -> Score
wrongAnswer score = record { wrongCount $= (+ 1 ) } score

Show Score where
  show (MkScore corrects wrongs) = show corrects ++ " / " ++ show (corrects + wrongs)

data NewScore : (rights : Nat) -> (wrongs: Nat) -> Type where
  Start : NewScore Z Z
  RightAnswer : (score : NewScore r w) -> NewScore (S r) w
  WrongAnswer : (score: NewScore r w) -> NewScore r (S w)

Show (NewScore r w) where
  show {r} {w} score = show r ++ " / " ++ show (r + w)

mutual
  correct : Stream Int -> (score : Score) -> ConsoleIO Score
  correct nums score = do PutStr "Correct!\n"
                          quiz nums (rightAnswer score)

  incorrect : Int -> Stream Int -> (score : Score) -> ConsoleIO Score
  incorrect answer nums score = do PutStr $ "Woops, the answer is " ++ show answer ++ "\n"
                                   quiz nums (wrongAnswer score)

  total
  quiz : Stream Int -> (score : Score) -> ConsoleIO Score
  quiz (num1 :: num2 :: nums) score
    = do PutStr ("Score so far: " ++ show score ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ " = ")
         case input of
           Answer i => if i == num1 * num2
                          then correct nums score
                          else incorrect (num1 * num2) nums score
           Quit => Quit score

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

data ShellInput = Cat String
                | Copy String String
                | Invalid
                | QuitShell

total
readShellInput : (prompt : String) -> Command ShellInput
readShellInput prompt = do PutStr prompt
                           cmd <- GetLine
                           case words cmd of
                             ["cat", fn] => Pure $ Cat fn
                             ["copy", src, dest] => Pure $ Copy src dest
                             ["quit"] => Pure QuitShell
                             _ => Pure Invalid

total
writeCommand : (dest : String) -> (contents : String) -> Command ()
writeCommand dest contents = do Right _ <- WriteFile (dest, contents)
                                  | Left err => PutStr ("Error writing file: " ++ show err ++ "\n")
                                Pure ()

mutual
  total
  processFile : (fn : String) -> (String -> Command ()) -> ConsoleIO ()
  processFile fn cont = do Right contents <- ReadFile fn
                             | Left err => do PutStr ("Error reading file: " ++ show err ++ "\n")
                                              simpleShell
                           cont contents
                           simpleShell

  total
  simpleShell : ConsoleIO ()
  simpleShell = do input <- readShellInput "> "
                   case input of
                     Invalid => do PutStr "Invalid command\n"
                                   simpleShell
                     Cat fn => processFile fn (\contents => PutStr $ contents ++ "\n")
                     Copy src dest => processFile src $ writeCommand dest
                     QuitShell => Quit ()

partial
main : IO ()
main = do Just _ <- run forever simpleShell
              | Nothing => putStrLn "Ran out of fuel"
          putStrLn "Ta-ta!"
