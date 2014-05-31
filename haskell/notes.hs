1 + 2   -- 3
3 * 4   -- 12
5 / 2   -- 2.5
div 5 2     -- 2
5 `div` 2   -- 2

True && True    -- True
False || False  -- False
not True        -- False

5 == 5          -- True
5 \= 5          -- False
"hello" == "hello"  -- True

succ 8          -- 9
succ 8.5        -- 9.5
succ 'h'        -- 'i'
succ "h"        -- Throws exception

min 9 10        -- 9
min 10 0.1      -- 0.1
min 1 2 3       -- Throws exception
max 1 2         -- 2

-- function application has higher precedence than operators
succ 9 * 8      -- 80
succ (9 * 8)    -- 73

[]              -- Empty List
[1, 2, 3]       -- list of numbers
[1, 2] ++ [3, 4]    -- [1, 2, 3, 4]
" hello " ++ " " ++ " world "   -- " hello world "
[ ’w ’ , ’o ’] ++ [ ’o ’ , ’t ’]    -- " woot "

-- : is the cons operator
5 : [1, 2, 3]       -- [5, 1, 2, 3]

-- !! is the index dereference operator
[1, 2, 3, 4] !! 2   -- 3

-- All the following are true.  Elements compared one by one using
-- comparison operator
[3 ,2 ,1] > [2 ,1 ,0]
[3 ,2 ,1] > [2 ,10 ,100]
[3 ,4 ,2] > [3 ,4]
[3 ,4 ,2] > [2 ,4]
[3 ,4 ,2] == [3 ,4 ,2]

head [1, 2, 3]      -- 1
tail [1, 2, 3]      -- [2, 3]
init [1, 2, 3]      -- [1, 2]
last [1, 2, 3]      -- 3

length [1, 2, 3]    -- 3
length []           -- 0

-- null checks if a list is empty
null []         -- True
null [1]        -- False
null [[]]       -- False

reverse [1, 2, 3]   -- [3, 2, 1]
take 3 [1..5]       -- [1, 2, 3]
take 10 [1..5]      -- [1..5]
drop 3 [1..5]       -- [4, 5]
drop 10 [1..5]      -- []
maximum [1..5]      -- 5
minimum [1..5]      -- 1
sum [1..5]          -- 15
product [1..5]      -- 120

-- elem function is like python's in operator
1 `elem` [1..5]     -- True
6 `elem` [1..5]     -- False
'h' `elem` [2..5]     -- Throws exception

-- Ranges
[2, 4..20]  -- [2 ,4 ,6 ,8 ,10 ,12 ,14 ,16 ,18 ,20]
[3, 6..20]  -- [3 ,6 ,9 ,12 ,15 ,18]
[5, 4..1]   -- [5, 4, 3, 2, 1]

-- Cycle makes an infinite list by repeating it's argument's elements over
-- and over
take 10 ( cycle [1 ,2 ,3])  -- [1 ,2 ,3 ,1 ,2 ,3 ,1 ,2 ,3 ,1]

take 10 ( repeat 5) -- [5 ,5 ,5 ,5 ,5 ,5 ,5 ,5 ,5 ,5]

-- List comprehensions
[x*x | x <- [1..10]]    -- [1,4,9,16,25,36,49,64,81,100]

-- With filter:
[x * 2 | x <- [1..10] , x * 2 >= 12]     -- [12 ,14 ,16 ,18 ,20]

-- With multiple predicates:
[ x | x <- [10..20] , x /= 13 , x /= 15 , x /= 19]  -- [10 ,11 ,12 ,14 ,16 ,17 ,18 ,20]

-- With multiple iterators:
[x * y | x <- [2 ,5 ,10] , y <- [8 ,10 ,11] , x * y > 50]   -- [55 ,80 ,100 ,110]

-- Tuples
-- * Can mix types
-- * Size is fixed
-- * No unary tuple
(1, 2)
('a', 3.0, 5)
zip [1, 2, 3] ['a', 'b', 'c']   -- [(1,'a'),(2,'b'),(3,'c')]
zip [1, 2, 3] ['a', 'b', 'c', 'd']   -- [(1,'a'),(2,'b'),(3,'c')]
fst (1, 2)      -- 1
snd (1, 2)      -- 2
fst (1, 2, 3)   -- Error

-- Types
--
-- GHCI command :t shows type of argument
--
-- Types are always capitalized, names/labels are always
-- lowercase/camelCase
-- :: is "has type of" operator
1 :: Int
1 :: Integer
1 :: Double     -- 1.0
1 :: Float      -- 1.0
'c' :: Char

removeNonUppercase :: [ Char ] -> [ Char ]
removeNonUppercase = [ c | c <- st , c ‘ elem ‘ [ ’A ’.. ’ Z ’]]

addThree :: Int -> Int -> Int -> Int
addThree x y z = x + y + z

-- Int - Machine integer type
-- Integer - Bignum integer type
-- Double
-- Float
-- Char
-- [ Char ] - String
-- Bool

-- Type variables
:t head     -- head :: [ a ] -> a

1 `compare` 2   -- LT
1 `compare` 1   -- EQ
2 `compare` 1   -- GT
:t 1 `compare` 2   -- Ordering

-- show typeclass - Anything with a toString function
show 3      -- "3"
show True   -- "True"

-- read typeclass - Anything with a parse function
read "True" :: Bool     -- True
read "3.2" :: Double    -- 3.2

-- Bounded - typeclass defining minBound and maxBound for bounded types
maxBound :: Int     -- 2^63 - 1 on 64 bit arch

-- Enum - typeclass defining pred and succ for enumerable types
-- Integral - Subclass of Num, applies to integers (Int and Integer)
-- fromIntegral - Promotes Integral to Num type so it can be combined with
--      other nums (essentially a casting operator)
-- 
