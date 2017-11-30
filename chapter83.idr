module Main

import Data.Vect

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

zeroNotSucc : (S k = 0) -> Void
zeroNotSucc Refl impossible

succNotZero : (0 = S k) -> Void
succNotZero Refl impossible

noRec : (contra : (j = k) -> Void) -> (S j = S k) -> Void
noRec contra Refl = contra Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat (S k) Z = No zeroNotSucc
checkEqNat Z (S k) = No succNotZero
checkEqNat (S j) (S k) = case checkEqNat j k of
                              Yes prf => Yes (cong prf)
                              No contra => No (noRec contra)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

dekEq : DecEq a => (val1 : Vect n a) -> (val2 : Vect n a) -> Dec (val1 = val2)
dekEq [] [] = Yes Refl
dekEq (x :: xs) (y :: ys) = case decEq x y of
                                 Yes prf => case dekEq xs ys of
                                                 Yes tailprf => Yes $ rewrite sym prf in cong tailprf
                                                 No contra => No $ tailUnequal contra
                                 No contra => No $ headUnequal contra
