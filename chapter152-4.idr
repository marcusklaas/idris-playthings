module Main

import ProcessLib

data ListAction : Type where
     Length : List elem -> ListAction
     Append : List elem -> List elem -> ListAction

ListType : ListAction -> Type
ListType (Length xs) = Nat
ListType (Append {elem} xs ys) = List elem

procList : Service ListType ()
procList = do Respond (\msg => case msg of
                                    Length l => Pure (length l)
                                    Append l1 l2 => Pure $ (++) l1 l2)
              Loop procList

procMain : Client ()
procMain = do Just server <- Spawn procList
                  | Nothing => (Action . putStrLn) "Spawn failed"
              len <- Request server (Length [1, 2, 3])
              Action . printLn $ len

              appendedList <- Request server (Append [2,3,5] [7])
              Action . printLn $ appendedList

record WCData where
       constructor MkWCData
       wordCount : Nat
       lineCount : Nat

doCount : (content : String) -> WCData
doCount content = let lineCount = length . lines $ content
                      werdCount = length . words $ content
                  in
                      MkWCData werdCount lineCount

data WC = CountFile String
        | GetData String

WCType : WC -> Type
WCType (CountFile _) = ()
WCType (GetData _) = Maybe WCData

countFile : (loaded : List (String, WCData)) ->
            (fname : String) ->
            Process WCType (List (String, WCData)) Sent Sent
countFile loaded fname
  = do Right content <- Action (readFile fname)
           | Left _ => Pure loaded
       let count = doCount content
       Action (putStrLn ("Counting complete for " ++ fname))
       Pure $ (fname, count) :: loaded

wcService : (loaded : List (String, WCData)) -> Service WCType ()
wcService loaded
  = do msg <- Respond (\msg => case msg of
                                    CountFile fname => Pure ()
                                    GetData fname => Pure $ lookup fname loaded)
       newLoaded <- case msg of
                         Just (CountFile fname) => countFile loaded fname
                         _ => Pure loaded
       Loop (wcService newLoaded)

wordCountClient : Client ()
wordCountClient = do Just wc <- Spawn (wcService Nil)
                         | Nothing => Action (putStrLn "Spawn failed")
                     Action (putStrLn "Counting ProcessLib.idr")
                     Request wc (CountFile "ProcessLib.idr")

                     Action (putStrLn "Processing")
                     Just wcData <- Request wc (GetData "ProcessLib.idr")
                         | Nothing => Action (putStrLn "Data not ready")
                     (Action . putStrLn) $ "Werds: " ++ (show . wordCount) wcData
                     (Action . putStrLn) $ "Lines: " ++ (show . lineCount) wcData
