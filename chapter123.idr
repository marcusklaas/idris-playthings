module Main

import Data.Primitives.Views
import System

record Score where
       constructor MkScore
       correct : Nat
       attempted : Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Int

initState : GameState
initState = MkGameState (MkScore Z Z) 12

setDifficulty : Int -> GameState -> GameState
setDifficulty k = record { difficulty = k }

addWrong : GameState -> GameState
addWrong = record { score->attempted $= S }

addCorrect : GameState -> GameState
addCorrect = addWrong . (record { score->correct $= S })

Show GameState where
  show st = show (correct $ score st) ++ "/" ++
            show (attempted $ score st) ++ "\n" ++
            "Difficulty: " ++ (show $ difficulty st)

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

Functor Command where
  map f command = Bind command (\x => Pure (f x))

Applicative Command where
  pure a = Pure a
  f <*> fa = Bind fa (\val => Bind f (\func => Pure (func val)))

Monad Command where
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

runCommand : Stream Int ->
             GameState ->
             Command a ->
             IO (a, Stream Int, GameState)
runCommand stream st (PutStr x) = do putStr x
                                     pure ((), stream, st)
runCommand stream st GetLine = do str <- getLine
                                  pure (str, stream, st)
runCommand (val :: stream) st GetRandom
  = pure (getRandom val (difficulty st), stream, st)
      where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1
runCommand stream st GetGameState = pure (st, stream, st)
runCommand stream st (PutGameState newSt) = pure ((), stream, newSt)
runCommand stream st (Pure val) = pure (val, stream, st)
runCommand stream st (Bind c f)
  = do (res, streamTail, newSt) <- runCommand stream st c
       runCommand streamTail newSt $ f res

run : Fuel ->
      Stream Int ->
      GameState ->
      ConsoleIO a ->
      IO (Maybe a, Stream Int, GameState)
run Dry stream st _ = pure (Nothing, stream, st)
run _ stream st (Quit x) = pure (Just x, stream, st)
run (More remainingFuel) stream st (Do y f)
  = do (res, streamTail, newSt) <- runCommand stream st y
       run remainingFuel streamTail newSt $ f res

data Input = Answer Int
           | QuitCmd

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = GetGameState >>= PutGameState . f

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               updateGameState addCorrect
               quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr $ "Oops, the answer was " ++ show ans ++ "\n"
                 updateGameState addWrong
                 quiz

  readInput : (prompt : String) -> Command Input
  readInput prompt = do PutStr prompt
                        res <- GetLine
                        if "quit" == res
                           then Pure QuitCmd
                           else Pure $ Answer $ cast res

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")

            input <- readInput (show num1 ++ " * " ++ show num2 ++ " = ")
            case input of
                 Answer answer => if answer == num1 * num2
                                     then correct
                                     else wrong (num1 * num2)
                 QuitCmd => Quit st

randoms : Int -> Stream Int
randoms seed = let nextSeed = 1664525 * seed + 1013904223 in
                   (shiftR nextSeed 2) :: randoms nextSeed

partial
main : IO ()
main = do seed <- time
          (Just score, _, state) <- run forever (randoms (fromInteger seed)) initState quiz
              | _ => putStrLn "Ran out of fuel"
          putStrLn $ "Final score: " ++ show state

record Votes where
       constructor MkVotes
       upvotes : Integer
       downvotes : Integer

record Article where
       constructor MkArticle
       title : String
       url : String
       score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

getScore : Article -> Integer
getScore x = let votes = score x in
               (upvotes votes) - (downvotes votes)

addUpvote : Article -> Article
addUpvote = record { score->upvotes $= (+1) }

addDownvote : Article -> Article
addDownvote = record { score->downvotes $= (+1) }
