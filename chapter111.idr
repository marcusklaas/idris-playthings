module Main

import Data.Primitives.Views

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs, ys, zs

Functor InfList where
    map func (value :: xs) = (func value) :: (map func xs)

countFrom : Integer -> InfList Integer
countFrom x = x :: countFrom (x + 1)

total
getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z stream = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs

naturals : Stream Nat
naturals = iterate S Z

total
labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith (value :: xs) [] = []
labelWith (value :: xs) (x :: ys) = (value, x) :: labelWith xs ys

label : List a -> List (Nat, a)
label = labelWith naturals

quiz : Stream Int -> (score : Nat) -> IO ()
quiz (num1 :: num2 :: nums) score
     = do putStrLn ("Score so far: " ++ show score)
          putStr (show num1 ++ " * " ++ show num2 ++ "? ")
          answer <- getLine
          if cast answer == num1 * num2
             then do putStrLn "Correct!"
                     quiz nums (score + 1)
             else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
                     quiz nums score

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

total
arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy _) = rem + 1

total
everyOther : Stream a -> Stream a
everyOther (value :: (x :: xs)) = x :: everyOther xs

data Face = Heads | Tails

total
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count stream = take count $ map getFace stream
  where
    getFace : Int -> Face
    getFace i with (divides i 2)
      getFace (_ + rem) | (DivBy _) = if rem == 0 then Heads
                                                  else Tails

squareRootApprox : (number : Double) -> (approx : Double) -> Stream Double
squareRootApprox number approx = approx :: (squareRootApprox number ((approx + number / approx) / 2))

total
squareRootBound : (maxIter : Nat) -> (number : Double) -> (dist : Double) -> (approxs : Stream Double) -> Double
squareRootBound Z number dist (value :: xs) = value
squareRootBound (S k) number dist (value :: xs)
                = if abs (value * value - number) <= dist
                     then value
                     else squareRootBound k number dist xs

total
squareRoot : Double -> Double
squareRoot x = squareRootBound 100000 x 0.00000001 (squareRootApprox x x)
