module Main

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

data Tree a = Empty
            | Node (Tree a) a (Tree a)

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left val right)
  = do left_labelled <- treeLabelWith left
       (this :: rest) <- get
       put rest
       right_labelled <- treeLabelWith right
       pure (Node left_labelled (this, val) right_labelled)

total
runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put x) st = ((), x)
runState (Pure x) st = (x, st)
runState (Bind x f) st = let (res, newSt) = runState x st
                           in
                         runState (f res) newSt

treeLabel : Tree a -> Tree (Integer, a)
treeLabel t = fst $ runState (treeLabelWith t) [1..]

crew : List String
crew = ["Lister", "Rimmer", "Kryten", "Cat"]

main : IO ()
main = do putStr "Display crew? "
          x <- getLine
          when (x == "yes") $
               do traverse putStrLn crew
                  pure ()
          putStrLn "Done"

addIfPositive : Integer -> State Integer Bool
addIfPositive x = do when (x > 0) $
                       do current <- get
                          put $ current + x
                     pure (x > 0)

addPositives : List Integer -> State Integer Nat
addPositives list = do added <- traverse addIfPositive list
                       (pure . length) $ filter id added
