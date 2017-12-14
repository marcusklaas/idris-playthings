module Main

data DoorCmd : Type where
     Open : DoorCmd ()
     Close : DoorCmd ()
     RingBell : DoorCmd ()

     Pure : ty -> DoorCmd ty
     (>>=) : DoorCmd a -> (a -> DoorCmd b) -> DoorCmd b

doorProg : DoorCmd ()
doorProg = do RingBell
              Open
              Close

data DoorState = DoorClosed | DoorOpen
