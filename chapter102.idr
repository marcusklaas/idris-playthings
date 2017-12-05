module Main

import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

data SnokList : List a -> Type where
     Empty : SnokList []
     Snoc : (rec : SnokList xs) -> SnokList (xs ++ [x])

snokListHelper : (snoc : SnokList input) -> (rest : List a) -> SnokList (input ++ rest)
snokListHelper {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snokListHelper {input} snoc (x :: xs) = rewrite (appendAssociative input [x] xs) in snokListHelper (Snoc snoc {x}) xs

snokList : (xs : List a) -> SnokList xs
snokList xs = snokListHelper Empty xs

myReverseHelper : (input : List a) -> SnokList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: (myReverseHelper xs rec)

myReverse : List a -> List a
myReverse input = myReverseHelper input (snokList input)

total
myReverseTwo : List a -> List a
myReverseTwo input with (snokList input)
  myReverseTwo [] | Empty = []
  myReverseTwo (xs ++ [x]) | (Snoc rec) = x :: myReverseTwo xs | rec

total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snokList input1)
  isSuffix [] input2 | Empty = True
  isSuffix (xs ++ [x]) input2 | (Snoc rec) with (snokList input2)
    isSuffix (xs ++ [x]) [] | (Snoc rec) | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) = y == x && isSuffix xs ys | xsrec | ysrec

mergeSort : Ord a => List a -> List a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (lefts ++ rights) | (SplitRecPair lrec rrec)
            = merge (mergeSort lefts | lrec) (mergeSort rights | rrec)

total
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc xrec) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc xrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xrec) | (Snoc yrec)
                = if x == y then (equalSuffix xs ys | xrec | yrec) ++ [x]
                            else []

total
mergeSortVects : Ord a => Vect n a -> Vect n a
mergeSortVects input with (splitRec input)
  mergeSortVects [] | SplitRecNil = []
  mergeSortVects [x] | SplitRecOne = [x]
  mergeSortVects (xs ++ ys) | (SplitRecPair lrec rrec)
                 = merge (mergeSortVects xs | lrec) (mergeSortVects ys | rrec)

total
toBinary : Nat -> String
toBinary n with (halfRec n)
  toBinary Z | HalfRecZ = ""
  toBinary (x + x) | (HalfRecEven rec) = (toBinary x | rec) ++ "0"
  toBinary (S (x + x)) | (HalfRecOdd rec) = (toBinary x | rec) ++ "1"

total
isPalindrome : Eq a => List a -> Bool
isPalindrome list with (vList list)
  isPalindrome [] | VNil = True
  isPalindrome [x] | VOne = True
  isPalindrome (x :: (xs ++ [y])) | (VCons rec)
               = if x == y then isPalindrome xs | rec
                           else False
