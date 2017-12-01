module Main

import Data.Vect

removeElem : (value : a) ->
             (xs : Vect (S n) a) ->
             (prf : Elem value xs) ->
             Vect n a
removeElem x (x :: xs) Here = xs
removeElem {n = Z} a (x :: []) (There later) = absurd later
removeElem {n = (S k)} a (x :: xs) (There later) = x :: removeElem a xs later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf

notHeadOrInTail : (c : (x = y) -> Void) -> (c_tail : Elem x xs -> Void) -> Elem x (y :: xs) -> Void
notHeadOrInTail c c_tail Here = c Refl
notHeadOrInTail c c_tail (There later) = c_tail later

izElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
izElem x [] = No absurd
izElem x (y :: xs) = case decEq x y of
                          Yes Refl => Yes Here
                          No contra => case (izElem x xs) of
                                            Yes prf => Yes $ There prf
                                            No contra_tail => No (notHeadOrInTail contra contra_tail)

data ListElem : a -> List a -> Type where
     Here : ListElem x (x :: xs)
     There : (later : ListElem x xs) -> ListElem x (y :: xs)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (y :: xs) value

proveNotLastEmptyList : Last [] value -> Void
proveNotLastEmptyList x impossible

singletonListNotLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
singletonListNotLast contra LastOne = contra Refl

proveNotLastTail : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
proveNotLastTail contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No proveNotLastEmptyList
isLast [x] value = case decEq x value of
                        Yes Refl => Yes LastOne
                        No contra => No (singletonListNotLast contra)
isLast (x :: (y :: xs)) value = case isLast (y :: xs) value of
                                     Yes prf => Yes $ LastCons prf
                                     No contra => No (proveNotLastTail contra)
