module Main

import Data.Vect

typeReverse : Nat -> Nat
typeReverse Z = Z
typeReverse (S n) = typeReverse n + 1

indexIt : Fin n -> Vect n a -> a
indexIt FZ (x :: xs) = x
indexIt (FS m) (x :: xs) = index m xs

reverseIt : Vect m elem -> Vect (typeReverse m) elem
reverseIt Nil = []
reverseIt (x :: xs) = (reverseIt xs) ++ [x]

innerProduct : Num a => Vect n a -> Vect n a -> a
innerProduct Nil Nil = 0
innerProduct (x :: xs) (y :: ys) = x * y + innerProduct xs ys

transposeHelper : Vect m a -> Vect m (Vect p a) -> Vect m (Vect (S p) a)
transposeHelper Nil Nil = Nil
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: (transposeHelper xs ys)

transposeIt : Vect n (Vect m a) -> Vect m (Vect n a)
transposeIt Nil = replicate _ []
transposeIt (x :: xs) = transposeHelper x (transpose xs)

matMult : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
matMult Nil rhs = Nil
matMult (x :: xs) rhs = (map (innerProduct x) (transpose rhs)) :: (matMult xs rhs)
