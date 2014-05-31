doubleMe x = x + x

doubleSmallNumber x = if x > 100
                          then x
                          else 2 * x

doubleUs x y = 2 * x + 2 * y


addThree :: Int -> Int -> Int -> Int
addThree x y z = x + y + z
