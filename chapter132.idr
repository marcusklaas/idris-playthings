module Main

import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
     Push : Integer -> StackCmd () height (S height)
     Pop : StackCmd Integer (S height) height
     Peek : StackCmd Integer (S height) (S height)

     GetStr : StackCmd String height height
     PutStr : String -> StackCmd () height height

     Pure : ty -> StackCmd ty height height
     (>>=) : StackCmd a height1 height2 ->
             (a -> StackCmd b height2 height3) ->
             StackCmd b height1 height3

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Peek = pure (x, x :: xs)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do (res, resStk) <- runStack stk x
                            runStack resStk (f res)
runStack stk GetStr = getLine >>= (\str => pure (str, stk))
runStack stk (PutStr str) = map (\x => (x, stk)) $ putStr str

doBinary : (Integer -> Integer -> Integer) -> StackCmd () (S $ S height) (S height)
doBinary f = do val1 <- Pop
                val2 <- Pop
                Push (f val1 val2)

data StackIO : Nat -> Type where
     Quit : StackIO height
     Do : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) ->
          StackIO height1

namespace StackDo
     (>>=) : StackCmd a height1 height2 ->
             (a -> Inf (StackIO height2)) ->
             StackIO height1
     (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

total
run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry _ _ = pure ()
run _ _ Quit = putStrLn "Ta-ta!"
run (More fuel) stk (Do val cont) = do (res, newStk) <- runStack stk val
                                       run fuel newStk (cont res)

data StkInput = Number Integer
              | Add
              | Subtract
              | Multiply
              | Negate
              | Discard
              | Duplicate
              | QuitCmd

strToInput : String -> Maybe StkInput
strToInput "quit" = Just QuitCmd
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput "subtract" = Just Subtract
strToInput "negate" = Just Negate
strToInput "multiply" = Just Multiply
strToInput "add" = Just Add
strToInput "" = Nothing
strToInput str = if all isDigit $ unpack str
                    then Just $ Number $ cast str
                    else Nothing

mutual
  tryBinary : (Integer -> Integer -> Integer) -> StackIO height
  tryBinary {height = S $ S _} f = do doBinary f
                                      result <- Peek
                                      PutStr (show result ++ "\n")
                                      stackCalc
  tryBinary _ = do PutStr "Need at least two items on stack\n"
                   stackCalc

  tryUnary : (Integer -> Integer) -> StackIO height
  tryUnary {height = S _} f = do val <- Pop
                                 let res = f val
                                 PutStr (show res ++ "\n")
                                 Push res
                                 stackCalc
  tryUnary _ = do PutStr "Need at least one item on stack\n"
                  stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = S _} = do val <- Pop
                                 PutStr ("Discarded " ++ show val ++ "\n")
                                 stackCalc
  tryDiscard = do PutStr "Cannot discard when stack is empty\n"
                  stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = S _} = do val <- Peek
                                   PutStr ("Duplicated " ++ show val ++ "\n")
                                   Push val
                                   stackCalc
  tryDuplicate = do PutStr "Cannot duplicate on empty stack\n"
                    stackCalc

  total
  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr

                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just QuitCmd => Quit
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Duplicate => tryDuplicate
                      Just Discard => tryDiscard
                      Just Add => tryBinary (+)
                      Just Multiply => tryBinary (*)
                      Just Subtract => tryBinary (-)
                      Just Unary => tryUnary (* -1)

main : IO ()
main = run forever [] stackCalc
