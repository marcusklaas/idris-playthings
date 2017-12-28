module Main

import System.Concurrency.Channels

data Fuel = Dry | More (Lazy Fuel)

data MessagePID : (iface : reqType -> Type) -> Type where
     MkMessage : PID -> MessagePID iface

data ProcState = NoRequest | Sent | Complete

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add x y) = Nat

data Process : (iface : reqType -> Type) ->
               Type ->
               (inState : ProcState) ->
               (outState : ProcState) ->
               Type where
     Request : MessagePID serviceIface ->
               (msg : serviceReqType) ->
               Process iface (serviceIface msg) st st
     Respond : ((msg : reqType) -> Process iface (iface msg) NoRequest NoRequest) ->
               Process iface (Maybe reqType) st Sent
     Spawn : Process serviceIface () NoRequest Complete ->
             Process iface (Maybe (MessagePID serviceIface)) st st
     Loop : Inf (Process iface a NoRequest Complete) ->
            Process iface a Sent Complete
     Action : IO a -> Process iface a st st
     Pure : a -> Process iface a st st
     (>>=) : Process iface a stateOne stateTwo ->
             (a -> Process iface b stateTwo stateThree) ->
             Process iface b stateOne stateThree

total
run : Fuel -> Process iface t inState outState -> IO (Maybe t)
run Dry _ = pure Nothing
run (More _) (Request {serviceIface} (MkMessage process) msg)
  = do Just chan <- connect process
           | Nothing => pure Nothing
       ok <- unsafeSend chan msg
       if ok then unsafeRecv (serviceIface msg) chan
             else pure Nothing
run (More fuel) (Respond {reqType} f)
  = do Just sender <- listen 1
           | Nothing => (pure . Just) Nothing
       Just msg <- unsafeRecv reqType sender
           | Nothing => (pure . Just) Nothing
       Just res <- run fuel (f msg)
           | Nothing => pure Nothing
       unsafeSend sender res
       pure . Just . Just $ msg
run (More fuel) (Spawn service)
  = do Just pid <- spawn $ do run fuel service
                              pure ()
           | Nothing => pure Nothing
       pure . Just . Just . MkMessage $ pid
run (More fuel) (Loop process)
  = run fuel process
run (More _) (Action action)
  = map Just action
run (More fuel) (Pure a)
  = pure . Just $ a
run (More fuel) (proc >>= f)
  = do Just res <- run fuel proc
           | Nothing => pure Nothing
       (run fuel) . f $ res

forever : Fuel
forever = More forever

partial
runProc : Process iface () inState outState -> IO ()
runProc proc = do run forever proc
                  pure ()

NoRecv : Void -> Type
NoRecv = const Void

Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

procAdder : Service AdderType ()
procAdder = do Respond (\(Add x y) => Pure (x + y))
               Loop procAdder

procMain : Client ()
procMain = do Just adderId <- Spawn procAdder
                  | Nothing => Action (putStrLn "Failed spawning process")
              res <- Request adderId (Add 10 500)
              Action (putStrLn . show $ res)
