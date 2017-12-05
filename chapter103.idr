module Main

import DataStore
import Shape_abs

testStore : DataStore (SString .+. SString .+. SInt)
testStore = addToStore ("Mercury", "Mariner 10", 1974)
            (addToStore ("Venus", "Venera", 1961)
            (addToStore ("Uranus", "Voyager 2", 1986)
            (addToStore ("Pluto", "New Horizons", 2015)
            empty)))

listItems : DataStore schema -> List (SchemaType schema)
listItems store with (storeView store)
  listItems store | SNil = []
  listItems (addToStore value subStore) | (SAdd rec) = value :: listItems subStore | rec

total
filterKeys : (test : SchemaType val_schema -> Bool) -> DataStore (SString .+. val_schema) -> List String
filterKeys test store with (storeView store)
  filterKeys test store | SNil = []
  filterKeys test (addToStore (MkPair key value) subStore) | (SAdd rec)
    = if test value then key :: (filterKeys test subStore | rec)
                    else (filterKeys test subStore | rec)

testStoreTwo : DataStore (SString .+. SInt)
testStoreTwo = addToStore ("First", 1) $
               addToStore ("Second", 2) $
               empty

total
getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues store with (storeView store)
  getValues store | SNil = []
  getValues (addToStore (MkPair str i) subStore) | (SAdd rec) = i :: getValues subStore | rec

total
area : Shape -> Double
area s with (shapeView s)
  area (triangle x y) | STriangle = x * y / 2.0
  area (rectangle x y) | SRectangle = x * y
  area (circle z) | SCircle = z * z * 3.1415
