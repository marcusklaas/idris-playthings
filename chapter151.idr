module Main

import System.Concurrency.Channels

data Message = Add Nat Nat

adder : IO ()
adder = do Just senderChan <- listen 1
               | Nothing => adder
           Just (Add x y) <- unsafeRecv Message senderChan
               | Nothing => adder
           ok <- unsafeSend senderChan (x + y)
           adder

main : IO ()
main = do Just adderId <- spawn adder
              | Nothing => putStrLn "Spawn failed"
          Just chan <- connect adderId
              | Nothing => putStrLn "Failed connection to adder"
          unsafeSend chan (Add 2 3)
          Just answer <- unsafeRecv Nat chan
              | Nothing => putStrLn "Failed receiving message"
          printLn answer
