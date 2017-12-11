module Main

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
