module Main

import Data.Vect

PIN : Type
PIN = Vect 4 Char

data ATMState = Ready | CardInserted | Session

data PINCheck = CorrectPIN | IncorrectPIN

data HasCard : ATMState -> Type where
     HasCI      : HasCard CardInserted
     HasSession : HasCard Session

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
     InsertCard : ATMCmd () Ready (const CardInserted)
     EjectCard  : {auto prf : HasCard state} -> ATMCmd () state  (const Ready)
     GetPIN     : ATMCmd PIN CardInserted (const CardInserted)

     CheckPIN  : PIN -> ATMCmd PINCheck CardInserted
                                        (\check => case check of
                                                        CorrectPIN => Session
                                                        IncorrectPIN => CardInserted)
     GetAmount : ATMCmd Nat state (const state)

     Dispense : (amount : Nat) -> ATMCmd () Session (const Session)

     Message : String -> ATMCmd () state (const state)
     Pure : (res : ty) -> ATMCmd ty (stateFn res) stateFn
     (>>=) : ATMCmd a state1 state2Fn ->
             ((res : a) -> ATMCmd b (state2Fn res) state3Fn) ->
             ATMCmd b state1 state3Fn

atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         pinOK <- CheckPIN pin
         case pinOK of
              CorrectPIN => do cash <- GetAmount
                               Dispense cash
                               EjectCard
              IncorrectPIN => do Message "Incorrect PIN. Ejecting card"
                                 EjectCard

testPIN : PIN
testPIN = ['1', '3', '3', '7']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = pure Nil
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure $ ch :: chs

runATM : ATMCmd res instate outStateFn -> IO res
runATM InsertCard = do putStrLn "Please insert your card (press enter)"
                       getLine >>= (const . pure) ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPIN = do putStr "Enter PIN: "
                   readVect 4
runATM (CheckPIN pin) = if pin == testPIN
                           then pure CorrectPIN
                           else pure IncorrectPIN
runATM GetAmount = do putStrLn "How much do you wish to withdraw?"
                      cash <- getLine
                      pure $ cast cash
runATM (Dispense amount) = do putStrLn $ "Dispensing " ++ show amount
runATM (Message x) = putStrLn x
runATM (Pure res) = pure res
runATM (x >>= f) = do x' <- runATM x
                      runATM $ f x'

main : IO ()
main = runATM atm

data Access = LoggedOut | LoggedIn
data PwdCheck = Correct | Incorrect

namespace Shell
  data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
       Password : String -> ShellCmd PwdCheck LoggedOut
                                              (\check => case check of
                                                              Correct => LoggedIn
                                                              Incorrect => LoggedOut)
       Logout : ShellCmd () LoggedIn (const LoggedOut)
       GetSecret : ShellCmd String LoggedIn (const LoggedIn)

       PutStr : String -> ShellCmd () state (const state)
       Pure : (res : ty) -> ShellCmd ty (stateFn res) stateFn
       (>>=) : ShellCmd a state1 state2Fn ->
               ((res : a) -> ShellCmd b (state2Fn res) state3Fn) ->
               ShellCmd b state1 state3Fn

session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "wurzel"
                 | Incorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr ("Secret: " ++ show msg ++ "\n")
             Logout

-- should not typeck
-- badSession : ShellCmd () LoggedOut (const LoggedOut)
-- badSession = do Password "wurzel"
--                 msg <- GetSecret
--                 PutStr ("Secret: " ++ show msg ++ "\n")
--                 Logout

-- should not typeck
-- noLogout : ShellCmd () LoggedOut (const LoggedOut)
-- noLogout = do Correct <- Password "wurzel"
--                   | Incorrect => PutStr "Wrong password"
--               msg <- GetSecret
--               PutStr ("Secret: " ++ show msg ++ "\n")

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data CoinResult = CoinAccepted | CoinRejected

namespace MachineCmd
  data MachineCmd : (ty : Type) ->
                    VendState ->
                    (ty -> VendState) ->
                    Type where
       InsertCoin : MachineCmd CoinResult (pounds, chocs)
                                          (\coinResult => case coinResult of
                                                               CoinAccepted => (S pounds, chocs)
                                                               CoinRejected => (pounds, chocs))
       VendChoc   : MachineCmd () (S pounds, S chocs) $ const (pounds, chocs)
       GetCoins   : MachineCmd () (pounds, chocs)     $ const (Z, chocs)
       Refill : (bars : Nat) -> MachineCmd () (Z, chocs) $ const (Z, bars + chocs)

       Display : String -> MachineCmd () state $ const state
       GetInput : MachineCmd (Maybe Input) state $ const state

       Pure : (res: ty) -> MachineCmd ty (stateFn res) stateFn
       (>>=) : MachineCmd a state1 state2Fn ->
               ((res : a) -> MachineCmd b (state2Fn res) state3Fn) ->
               MachineCmd b state1 state3Fn

namespace MachineDo
  data MachineIO : VendState -> Type where
       Do : MachineCmd a state1 state2Fn ->
            ((res : a) -> Inf (MachineIO $ state2Fn res)) ->
            MachineIO state1

  (>>=) : MachineCmd a state1 state2Fn ->
          ((res : a) -> Inf (MachineIO $ state2Fn res)) ->
          MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = S k} {chocs = S j} = do VendChoc
                                         Display "Enjoy!"
                                         machineLoop
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of chocolates"
                        machineLoop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill {pounds = (S k)} num = do Display "Cannot refill with coins in machine"
                                   machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop
    = do Just x <- GetInput
            | Nothing => do Display "Invalid input"
                            machineLoop

         case x of
              COIN => do CoinAccepted <- InsertCoin
                             | CoinRejected => do Display "Coin rejected"
                                                  machineLoop
                         machineLoop
              VEND => vend
              CHANGE => do GetCoins
                           Display "Change returned"
                           machineLoop
              REFILL num => refill num
