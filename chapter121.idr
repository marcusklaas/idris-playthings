module Main

import Control.Monad.State

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = Nil
flatten (Node left val right) = flatten left ++ val :: flatten right

treeLabelWith : Stream labelType -> Tree a -> (Stream labelType, Tree (labelType, a))
treeLabelWith stream Empty = (stream, Empty)
treeLabelWith labels (Node left val right)
  = let (thisLabel :: restLabels, leftTree) = treeLabelWith labels left
        (remainingLabels, rightTree) = treeLabelWith restLabels right
            in
        (remainingLabels, Node leftTree (thisLabel, val) rightTree)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel = snd . (treeLabelWith [1..])

increase : Nat -> State Nat ()
increase inc = do current <- get
                  put $ current + inc

total
statefulTreeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
statefulTreeLabelWith Empty = pure Empty
statefulTreeLabelWith (Node leftTree value rightTree)
  = do labeledLeft <- statefulTreeLabelWith leftTree
       (thisLabel :: rest) <- get
       put rest
       labeledRight <- statefulTreeLabelWith rightTree
       pure (Node labeledLeft (thisLabel, value) labeledRight)

statefulTreeLabel : Tree a -> Tree (Integer, a)
statefulTreeLabel tr = evalState (statefulTreeLabelWith tr) [1..]

update : (stateType -> stateType) -> State stateType ()
update f = map f get >>= put

newIncrease : Nat -> State Nat ()
newIncrease = update . (+)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = newIncrease (S Z)
countEmpty (Node leftTree _ rightTree)
  = do countEmpty leftTree
       countEmpty rightTree

total
countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do (empties, nodes) <- get
                          put $ (S empties, nodes)
countEmptyNode (Node leftTree val rightTree)
  = do countEmptyNode leftTree
       countEmptyNode rightTree
       (empties, nodes) <- get
       put $ (empties, S nodes)
