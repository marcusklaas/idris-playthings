module Main

data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total
describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty! Initial portion: " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          NonEmpty ys y => NonEmpty (x :: ys) y

total
describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

total
describeList : List Int -> String
describeList xs with (listLast xs)
  describeList [] | Empty = "Empty"
  describeList (ys ++ [x]) | (NonEmpty _ _) = "Non-empty! Initial portion: " ++ show ys

myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: (myReverse ys)

data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights: List a) -> SplitList (lefts ++ rights)

total
splitList : (input : List a) -> SplitList input
splitList xs = splitListHelp xs xs where
  splitListHelp : List a -> (input : List a) -> SplitList input
  splitListHelp _ [] = SplitNil
  splitListHelp _ (x :: []) = SplitOne
  splitListHelp (_ :: _ :: counter) (item :: items)
    = case splitListHelp counter items of
           SplitNil => SplitOne -- this shouldn't be possible, right?
           SplitOne {x} => SplitPair [item] [x]
           SplitPair lefts rights => SplitPair (item :: lefts) rights
  splitListHelp _ items = SplitPair [] items

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair _ _) = merge (mergeSort lefts) (mergeSort rights) where
      merge : Ord a => List a -> List a -> List a
      merge [] xs = xs
      merge xs [] = xs
      merge (x :: xs) (y :: ys) = if x < y then
                                     x :: (merge xs (y :: ys))
                                  else
                                     y :: (merge (x :: xs) ys)

data TakeN : List a -> Type where
     Fewer : TakeN xs
     Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (y :: ys) = case takeN k ys of
                             Fewer => Fewer
                             Exact pref => Exact (y :: pref)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact _) = n_xs :: (groupByN n rest)

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
