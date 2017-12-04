module Main

import Data.Vect
import chapter91

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]

noMultiLetterValid : ValidInput (x :: (y :: xs)) -> Void
noMultiLetterValid inp impossible

noEmptyLetterValid : ValidInput [] -> Void
noEmptyLetterValid input impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No noEmptyLetterValid
isValidInput (x :: []) = Yes $ Letter x
isValidInput (x :: (y :: xs)) = No noMultiLetterValid

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString (toUpper x) of
                    Yes prf => pure (_ ** prf)
                    No contra => do putStrLn "Invalid guess"
                                    readGuess

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess l (MkWordState word missing) = case isElem l missing of
                                                 Yes prf => Right $ MkWordState word (chapther91.removeElem_auto l missing)
                                                 No contra => Left $ MkWordState word missing

game : WordState (S guesses) (S letters) -> IO Finished
game st = ?game_rhs
