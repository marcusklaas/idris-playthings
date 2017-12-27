module Main

import System.Concurrency.Channels

%default total

data MessagePID = MkMessage PID

data Message = Msg Nat Nat

data Process : Type -> Type where
     Request : MessagePID -> Message -> Process (Maybe Nat)
     Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)
     Spawn : Process () -> Process (Maybe MessagePID)
     Action : IO a -> Process a
     Loop : Inf (Process a) -> Process a
     Pure : a -> Process a
     (>>=) : Process a -> (a -> Process b) -> Process b

data Fuel = Dry | More (Lazy Fuel)

-- is this a bug in Idris 1.0? this should be considered total!
partial
run : Fuel -> Process t -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Action act) = act >>= pure . Just
run fuel (Pure val) = pure . Just $ val
run fuel (act >>= next) = do Just res <- run fuel act
                                 | Nothing => pure Nothing
                             run fuel $ next res
run fuel (Spawn proc) = do Just pid <- spawn $ map (const ()) (run fuel proc)
                               | Nothing => pure Nothing
                           pure . Just . Just . MkMessage $ pid
run fuel (Request (MkMessage pid) msg)
    = do Just chan <- connect pid
             | Nothing => pure (Just Nothing)
         ok <- unsafeSend chan msg
         if ok then do Just x <- unsafeRecv Nat chan
                           | Nothing => pure (Just Nothing)
                       pure . Just . Just $ x
               else pure (Just Nothing)
run fuel (Respond f) = do Just sender <- listen 1
                              | Nothing => pure (Just Nothing)
                          Just msg <- unsafeRecv Message sender
                              | Nothing => pure (Just Nothing)
                          Just res <- run fuel . f $ msg
                              | Nothing => pure (Just Nothing)
                          unsafeSend sender res
                          pure . Just . Just $ msg
run (More fuel) (Loop act) = run fuel act

procAdder : Process ()
procAdder = do Respond (\(Msg x y) => Pure $ x + y)
               Loop procAdder

procMain : Process ()
procMain = do Just adderId <- Spawn procAdder
                  | Nothing => Action (putStrLn "Failed spawning process")
              Just res <- Request adderId (Msg 10 500)
                  | Nothing => Action (putStrLn "Failed receiving msg")
              Action (putStrLn . show $ res)

partial
forever : Fuel
forever = More forever

-- should be total!
partial
runProc : Process () -> IO ()
runProc proc = do run forever proc
                  pure ()

data ProcState = NoRequest | Sent | Complete

data NewProcess : Type ->
                  (inState : ProcState) ->
                  (outState : ProcState) ->
                  Type where
     Request : MessagePID -> Message -> NewProcess Nat st st
     Respond : ((msg : Message) -> NewProcess Nat NoRequest NoRequest) ->
               NewProcess (Maybe Message) st Sent
     Spawn : NewProcess () NoRequest Complete ->
             NewProcess (Maybe MessagePID) st st
     Loop : Inf (NewProcess a NoRequest Complete) ->
            NewProcess a Sent Complete
     Action : IO a -> NewProcess a st st
     Pure : a -> NewProcess a st st
     (>>=) : NewProcess a stateOne stateTwo ->
             (a -> NewProcess stateTwo stateThree) ->
             NewProcess b stateOne stateThree
