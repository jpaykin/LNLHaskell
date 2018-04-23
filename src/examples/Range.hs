module Range where

import Test.QuickCheck


-- Range: A set library based on ranges of integers

-- a range (min,max) equates to the list [min..max], INCLUSIVE
type Range = (Int,Int)
type RSet = [Range]

validRange :: Range -> Bool
validRange (min,max) = 0 <= min && min <= max

validRSet :: RSet -> Bool
validRSet []                         = True
validRSet [(min,max)]                = validRange (min,max)
validRSet ((min,max):(min',max'):rs) = 
            validRange (min,max) && min' > max+1 && validRSet ((min',max'):rs)


-- requirement: if validRange r and validRSet rs then validRange (insertRange r rs)
insertRange :: Range -> RSet -> RSet
insertRange (min0,max0) [] = [(min0,max0)]
insertRange (min0,max0) ((min1,max1) : rs) 
    -- (min0,max0) comes before everything in (min1,max1)
    | max0+1 < min1  = (min0,max0) : (min1,max1) : rs
    -- (min0,max0) overlaps with (min1,max1)
    -- TODO: check these bounds
    | max0+1 >= min1 && min0 <= max1+1 = insertRange (min min0 min1, max max0 max1) rs
    -- (min0,max0) comes after everything in (min1,max1)
    | min0 > max1+1 = (min1,max1) : insertRange (min0,max0) rs
    | otherwise     = error "ill defined range"

mergeRSet :: RSet -> RSet -> RSet
mergeRSet [] r = r
mergeRSet ((min,max) : r1) r2 = insertRange (min,max) (mergeRSet r1 r2)

inRange :: Int -> Range -> Bool
inRange i (min,max) = min <= i && i <= max

inRSet :: Int -> RSet -> Bool
inRSet _ [] = False
inRSet i (r:rs) = inRange i r || inRSet i rs

sizeRange :: Range -> Int
sizeRange (min,max) = max-min+1

sizeRSet :: RSet -> Int
sizeRSet [] = 0
sizeRSet (r:rs) = sizeRange r + sizeRSet rs

-- given an index i with i < sizeRange r, 
-- offsetRange i r gives the ith element in r 
offsetRange :: Int -> Range -> Int
offsetRange i r = i + fst r

offsetRSet :: Int -> RSet -> Int
offsetRSet _ []     = 0
offsetRSet i (r:rs) | i < sizeRange r = offsetRange i r
                      | otherwise       = offsetRSet (i + sizeRange r) rs

offsetRangeInProp :: Int -> Range -> Bool
offsetRangeInProp i r = 
    (0 <= i && validRange r && i < sizeRange r) <= inRange (offsetRange i r) r

offsetRSetInProp :: Int -> RSet -> Bool
offsetRSetInProp i rs = (0 <= i && validRSet rs && i < sizeRSet rs) 
                        <= inRSet (offsetRSet i rs) rs

insertRangeProp :: Range -> RSet -> Bool
insertRangeProp r rs = 
  (validRange r && validRSet rs) <= validRSet (insertRange r rs)

insertRangeProp2 :: Int -> Range -> RSet -> Bool
insertRangeProp2 i r rs = (inRange i r || inRSet i rs) == inRSet i (insertRange r rs)

mergeRSetProp :: RSet -> RSet -> Bool
mergeRSetProp rs1 rs2 = 
    (validRSet rs1 && validRSet rs2) <= validRSet (mergeRSet rs1 rs2)

mergeRSetProp2 :: Int -> RSet -> RSet -> Bool
mergeRSetProp2 i rs1 rs2 = 
    (inRSet i rs1 || inRSet i rs2) == inRSet i (mergeRSet rs1 rs2)


splitRSet :: Int -> RSet -> (RSet,RSet)
splitRSet _ []                         = ([],[])
splitRSet i ((min,max):rs) | i <= min  = ([],(min,max):rs)
                             | i <= max  = ([(min,i-1)], (i,max):rs)
                             | otherwise = let (rs1,rs2) = splitRSet i rs 
                                           in ((min,max):rs1,rs2)

splitRSetValid :: Int -> RSet -> Bool
splitRSetValid i rs = validRSet rs <= (  validRSet (fst (splitRSet i rs))
                                          && validRSet (snd (splitRSet i rs)) )

splitRSetProp1 :: Int -> Int -> RSet -> Bool
splitRSetProp1 i j rs = 
    validRSet rs <= 
    ((inRSet i rs && i < j) == inRSet i (fst (splitRSet j rs)))


splitRSetProp2 :: Int -> Int -> RSet -> Bool
splitRSetProp2 i j rs = 
    validRSet rs <= 
    ((inRSet i rs && i >= j) == inRSet i (snd (splitRSet j rs)))


rangesTests = do print $ "Testing insertRangeProp"
                 quickCheck insertRangeProp
                 print $ "Testing insertRangeProp2"
                 quickCheck insertRangeProp2
                 print $ "Testing mergeRSetProp"
                 quickCheck mergeRSetProp
                 print $ "Testing mergeRSetProp2"
                 quickCheck mergeRSetProp2
                 print $ "Testing splitRSetValid"
                 quickCheck splitRSetValid
                 print $ "Testing splitRSetProp1"
                 quickCheck splitRSetProp1
                 print $ "Testing splitRSetProp2"
                 quickCheck splitRSetProp2
                 print $ "Testing offsetRangeInProp"
                 quickCheck offsetRangeInProp
                 print $ "Testing offsetRSetInProp"
                 quickCheck offsetRSetInProp
