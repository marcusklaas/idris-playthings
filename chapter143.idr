module Main

import Data.Vect

%default total

data GameState : Type where
     NotRunning : GameState
     Running : (guesses : Nat) -> (letters : Nat) -> GameState

letters : String -> List Char
letters = nub . (map toUpper) . unpack

data GuessResult = GoodGuess | BadGuess

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
     NewGame : (word : String) -> GameCmd () NotRunning
                                             (const $ Running 6 $ length $ letters word)
     Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
     Lost : GameCmd () (Running Z (S letters)) (const NotRunning)
     Guess : Char -> GameCmd GuessResult (Running (S guesses) (S letters))
                                 (\res => case res of
                                               GoodGuess => Running (S guesses) letters
                                               BadGuess => Running guesses (S letters))

     ShowState : GameCmd () state (const state)
     Message : String -> GameCmd () state (const state)
     ReadGuess : GameCmd Char state (const state)

     Pure : (res : ty) -> GameCmd ty (stateFn res) stateFn
     (>>=) : GameCmd a state1 state2Fn ->
             ((res : a) -> GameCmd b (state2Fn res) state3Fn) ->
             GameCmd b state1 state3Fn

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
       (>>=) : GameCmd a state1 state2Fn ->
               ((res : a) -> Inf (GameLoop b (state2Fn res) state3Fn)) ->
               GameLoop b state1 state3Fn
       Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters}
  = do ShowState
       g <- ReadGuess
       ok <- Guess g
       case ok of
            GoodGuess => case letters of
                              Z => do Won
                                      ShowState
                                      Exit
                              S k => do Message "Correct!"
                                        gameLoop
            BadGuess => case guesses of
                             Z => do Lost
                                     ShowState
                                     Exit
                             S k => do Message "No good!"
                                       gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing"
             gameLoop

data Game : GameState -> Type where
     GameStart : Game NotRunning
     GameWon : (word : String) -> Game NotRunning
     GameLost : (word : String) -> Game NotRunning
     InProgress : (word : String) ->
                  (guesses : Nat) ->
                  (missing : Vect letters Char) ->
                  Game (Running guesses letters)

Show (Game g) where
  show GameStart = "Starting"
  show (GameWon word) = "Game won: word was " ++ word
  show (GameLost word) = "Game lost: word was " ++ word
  show (InProgress word guesses missing)
    = "\n" ++ pack (map hideMissing (unpack word))
      ++ "\n" ++ show guesses ++ " guesses left"
        where
      hideMissing : Char -> Char
      hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel)

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
     OK : (res : ty) ->
          Game (outstateFn res) ->
          GameResult ty outstateFn
     OutOfFuel : GameResult ty outstateFn

ok : (res : ty) -> Game (outstateFn res) -> IO (GameResult ty outstateFn)
ok res st = pure $ OK res st

removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: Nil) {prf = There later} = absurd later
removeElem {n = S k} value (y :: ys) {prf = There later} = y :: removeElem value ys

runCmd : Fuel ->
         Game instate ->
         GameCmd ty instate outstateFn ->
         IO (GameResult ty outstateFn)
runCmd Dry state cmd = pure OutOfFuel
runCmd (More x) state (NewGame word)
  = ok () (InProgress (toUpper word) _ (fromList $ letters word))
runCmd (More x) (InProgress word (S guesses) missing) Won
  = ok () (GameWon word)
runCmd (More x) (InProgress word Z missing) Lost
  = ok () (GameLost word)
runCmd (More fuel) (InProgress word _ missing) (Guess y)
  = case isElem y missing of
         Yes prf => ok GoodGuess (InProgress word _ (removeElem y missing))
         No contra => ok BadGuess (InProgress word _ missing)
runCmd (More x) state ShowState = do putStrLn $ show state
                                     ok () state
runCmd (More x) state (Message msg) = do putStrLn msg
                                         ok () state
runCmd (More fuel) state ReadGuess
  = do putStr "Guess: "
       input <- getLine
       case unpack input of
            [x] => if isAlpha x
                      then ok (toUpper x) state
                      else do putStrLn "Invalid input"
                              runCmd fuel state ReadGuess
            _ => do putStrLn "Invalid input"
                    runCmd fuel state ReadGuess
runCmd (More x) state (Pure res) = ok res state
runCmd (More fuel) state (y >>= f)
  = do OK cmdRes newSt <- runCmd fuel state y
           | OutOfFuel => pure OutOfFuel
       runCmd fuel newSt $ f cmdRes

run : Fuel ->
      Game instate ->
      GameLoop ty instate outstateFn ->
      IO (GameResult ty outstateFn)
run Dry game cmdStream = pure OutOfFuel
run (More fuel) game (x >>= f) = do OK cmdRes newSt <- runCmd fuel game x
                                        | OutOfFuel => pure OutOfFuel
                                    run fuel newSt $ f cmdRes
run (More fuel) game Exit = pure $ OK () game

%default partial

forever : Fuel
forever = More forever

main : IO ()
main = do run forever GameStart hangman
          pure ()
