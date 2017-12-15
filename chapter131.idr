module Main

namespace Door
  data DoorState = DoorClosed | DoorOpen

  data DoorCmd : Type ->
                 DoorState ->
                 DoorState ->
                 Type where
       Open : DoorCmd     () DoorClosed DoorOpen
       Close : DoorCmd    () DoorOpen DoorClosed
       RingBell : DoorCmd () st st

       Pure : ty -> DoorCmd ty state state
       (>>=) : DoorCmd a state1 state2 ->
               (a -> DoorCmd b state2 state3) ->
               DoorCmd b state1 state3

  doorProg : DoorCmd () DoorClosed DoorClosed
  doorProg = do RingBell
                Open
                RingBell
                Close

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type ->
                  VendState ->
                  VendState ->
                  Type where
     InsertCoin : MachineCmd () (pounds, chocs)     (S pounds, chocs)
     VendChoc   : MachineCmd () (S pounds, S chocs) (pounds, chocs)
     GetCoins   : MachineCmd () (pounds, chocs)     (Z, chocs)
     Refill : (bars : Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)

     Display : String -> MachineCmd () state state
     GetInput : MachineCmd (Maybe Input) state state

     Pure : ty -> MachineCmd ty state state
     (>>=) : MachineCmd a state1 state2 ->
             (a -> MachineCmd b state2 state3) ->
             MachineCmd b state1 state3

data MachineIO : VendState -> Type where
     Do : MachineCmd a state1 state2 ->
          (a -> Inf (MachineIO state2)) ->
          MachineIO state1

namespace MachineDo
     (>>=) : MachineCmd a state1 state2 ->
             (a -> Inf (MachineIO state2)) ->
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
              COIN => do InsertCoin
                         machineLoop
              VEND => vend
              CHANGE => do GetCoins
                           Display "Change returned"
                           machineLoop
              REFILL num => refill num

namespace Guesses
  data GuessCmd : Type -> Nat -> Nat -> Type where
       Try : Integer -> GuessCmd Ordering (S k) k

       Pure : ty -> GuessCmd ty state state
       (>>=) : GuessCmd a state1 state2 ->
               (a -> GuessCmd b state2 state3) ->
               GuessCmd b state1 state3

threeGuesses : GuessCmd () 3 0
threeGuesses = do Try 10
                  Try 20
                  Try 15
                  Pure ()

-- does not typeck
-- noGuesses : GuessCmd () Z Z
-- noGuesses = do Try 10
--                Pure ()

namespace Physics
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
       Melt : MatterCmd () Solid Liquid
       Boil : MatterCmd () Liquid Gas
       Freeze : MatterCmd () Liquid Solid
       Condense : MatterCmd () Gas Liquid

       (>>=) : MatterCmd a state1 state2 ->
               (a -> MatterCmd b state2 state3) ->
               MatterCmd b state1 state3

iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze

-- does not typeck
-- overMelt : MatterCmd () Solid Gas
-- overMelt = do Melt
--               Melt
