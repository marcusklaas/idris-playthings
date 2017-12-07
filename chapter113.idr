module Main

data RunIO : Type -> Type where
     Quit : a -> RunIO a
     Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

total
greet : RunIO ()
greet = do putStr "Enter your name: "
           name <- getLine
           if name == ""
              then do putStrLn "Bye bye!"
                      Quit ()
              else do putStrLn ("Hello " ++ name)
                      greet

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

total
run : Fuel -> RunIO a -> IO (Maybe a)
run Dry _ = pure Nothing
run (More _) (Quit io) = pure $ Just io
run (More f) (Do action cont) = do res <- action
                                   run f $ cont res

partial
main : IO ()
main = run forever greet >>= (const $ pure ())
