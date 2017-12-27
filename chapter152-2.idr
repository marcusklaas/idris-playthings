module Main

import System.Concurrency.Channels

data Fuel = Dry | More (Lazy Fuel)

data MessagePID = MkMessage PID

data Message = Msg Nat Nat

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
             (a -> NewProcess b stateTwo stateThree) ->
             NewProcess b stateOne stateThree

partial
run : Fuel -> NewProcess t inState outState -> IO (Maybe t)
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
             | Nothing => pure Nothing
         ok <- unsafeSend chan msg
         if ok then do Just x <- unsafeRecv Nat chan
                           | Nothing => pure Nothing
                       pure . Just $ x
               else pure Nothing
run fuel (Respond f) = do Just sender <- listen 1
                              | Nothing => pure (Just Nothing)
                          Just msg <- unsafeRecv Message sender
                              | Nothing => pure (Just Nothing)
                          Just res <- run fuel . f $ msg
                              | Nothing => pure (Just Nothing)
                          unsafeSend sender res
                          pure . Just . Just $ msg
run (More fuel) (Loop act) = run fuel act

partial
forever : Fuel
forever = More forever

-- should be total!
partial
runProc : NewProcess () inState outState -> IO ()
runProc proc = do run forever proc
                  pure ()

Service : Type -> Type
Service a = NewProcess a NoRequest Complete

Client : Type -> Type
Client a = NewProcess a NoRequest NoRequest

procAdder : Service ()
procAdder = do Respond (\(Msg x y) => Pure (x + y))
               Loop procAdder

procMain : Client ()
procMain = do Just adderId <- Spawn procAdder
                  | Nothing => Action (putStrLn "Failed spawning process")
              res <- Request adderId (Msg 10 500)
              Action (putStrLn . show $ res)

-- shouldnt typeck
-- badProcAdder : NewProcess () NoRequest Complete
-- badProcAdder = do Action (putStrLn "I'm out of the office today")
--                   Loop procAdder
