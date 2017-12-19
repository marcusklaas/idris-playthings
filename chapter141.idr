module Main

data DoorResult = OK | Jammed

data DoorState = DoorOpen | DoorClosed

data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
     Open : DoorCmd DoorResult DoorClosed
                               (\res => case res of
                                             OK => DoorOpen
                                             Jammed => DoorClosed)
     Close : DoorCmd () DoorOpen (const DoorClosed)
     RingBell : DoorCmd () DoorClosed (const DoorClosed)

     Display : String -> DoorCmd () state (const state)

     Pure : (res : ty) -> DoorCmd ty (stateFn res) stateFn
     (>>=) : DoorCmd a state1 state2Fn ->
             ((res : a) -> DoorCmd b (state2Fn res) state3Fn) ->
             DoorCmd b state1 state3Fn

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              jam <- Open
              case jam of
                   OK => Close
                   Jammed => Display "Door is jammed"
