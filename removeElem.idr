module Main

import Data.Vect

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

removeElem : DecEq a => a -> Vect (S n) a -> Vect n a
removeElem x (y :: xs) = xs

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS l l (Same l) = Same (S l)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case (checkEqNat k j) of
                              Nothing => Nothing
                              Just eq => Just (sameS _ _ eq)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat m len of
                                 Just (Same k) => Just input
                                 Nothing => Nothing

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons = cong

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl = cong

data ThreeEq : a -> b -> c -> Type where
  ThreeSame : ThreeEq a a a

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x ThreeSame = ThreeSame

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse {n = S k} (x :: xs) = rewrite (plusCommutative 1 k) in (myReverse xs ++ [x])

myReverseTwo : Vect n a -> Vect n a
myReverseTwo [] = []
myReverseTwo (x :: xs) = reverseProof (myReverseTwo xs ++ [x])
  where
    reverseProof : Vect (len + 1) a -> Vect (S len) a
    reverseProof {len} vec = rewrite plusCommutative 1 len in vec

appendProof : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
appendProof {m} {k} xs = rewrite sym (plusSuccRightSucc m k) in xs

append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append {m} [] ys = rewrite (plusCommutative m 0) in ys
append {n = S k} {m} (x :: xs) ys = appendProof (x :: (append xs ys))

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym $ plusZeroRightNeutral m
myPlusCommutes (S k) m = sym $ rewrite (myPlusCommutes k m) in (sym (plusSuccRightSucc m k))

myReverseThree : Vect k a -> Vect k a
myReverseThree xs = helper [] xs
  where
    helper : Vect n a -> Vect m a -> Vect (n + m) a
    helper {n} xs [] = rewrite (myPlusCommutes n 0) in xs
    helper {n} {m = S k} xs (y :: ys) = rewrite sym (plusSuccRightSucc n k) in (helper (y :: xs) ys)
