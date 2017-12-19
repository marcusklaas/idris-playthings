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
ok res st = pure (OK res st)

runCmd : Fuel ->
         Game instate ->
         GameCmd ty instate outstateFn ->
         IO (GameResult ty outstateFn)
runCmd Dry state cmd = pure OutOfFuel
runCmd (More x) state (NewGame word) = ?rhs_1
runCmd (More x) state Won = ?rhs_3
runCmd (More x) state Lost = ?rhs_4
runCmd (More x) state (Guess y) = ?rhs_5
runCmd (More x) state ShowState = ?rhs_6
runCmd (More x) state (Message y) = ?rhs_7
runCmd (More x) state ReadGuess = ?rhs_8
runCmd (More x) state (Pure res) = ?rhs_9
runCmd (More x) state (y >>= f) = ?rhs_10

run : Fuel ->
      Game instate ->
      GameLoop ty instate outstateFn ->
      IO (GameResult ty outstateFn)
run Dry game cmdStream = pure OutOfFuel
run (More fuel) game (x >>= f) = do OK cmdRes newSt <- runCmd fuel game x
                                        | OutOfFuel => pure OutOfFuel
                                    run fuel newSt $ f cmdRes
run (More fuel) game Exit = pure $ OK () game
