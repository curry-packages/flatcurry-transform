f :: Int -> Int
f x = id $ x + 1

g :: Bool -> Bool
g x = not $ (not :: Bool -> Bool) $ (x :: Bool)

add :: Int -> Int -> Int
add m n = ((+) $ m) $ n

h :: Int -> Int
h x = id $ (x :: Int)

case1 :: Bool
case1 = case True of False -> True
                     True  -> False

case2 :: Bool
case2 = case (True :: Bool) of False -> True
                               True  -> False
