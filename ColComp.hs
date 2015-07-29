{-# LANGUAGE OverloadedStrings #-}
import Haste.Events
import Haste.DOM
import Haste.Foreign
import Haste

import Data.Char (toUpper, toLower)
import Data.List.Split (splitOn)
import Data.List
import Data.Maybe (catMaybes)
import Numeric (showHex)
import Debug.Trace

toHex :: Int -> String
toHex i | i < 0 = error "no negatives allowed"
        | i >= 0  && i < 10 = show i
        | i >= 10 && i < 16 = (:"") $ ['A'..'F'] !! (i - 10)
toHex i = let (d, m) = (i `div` 16, i `mod` 16)
          in toHex d ++ toHex m

randomColour :: IO String
randomColour = do
  gen <- newSeed
  let r:g:b:_ = (randomRs (0,255) gen :: [Int])
  return $ '#':concatMap fix [r,g,b]
    where
      fix i = case toHex $ i `div` 2 + 128 of
        h:[] -> '0':h:[]
        str  -> take 2 str
    

main = do
  url <- urlHash
  let table = urlTable $ drop 1 url
  
  
  elems <- mapM elemById ["left", "right", "leftCol", "rightCol"]  
  case catMaybes elems of
   [left, right, leftCol, rightCol] -> do
     setCol left leftCol
     case lookup 'l' table of
      Just col -> setProp left "value" col
      Nothing  -> do col <- randomColour
                     setProp left "value" col
     case lookup 'r' table of
      Just col -> setProp right "value" col
      Nothing  -> do col <- randomColour
                     setProp right "value" col
     
     setCol left leftCol
     setCol right rightCol
     left `onEvent` KeyUp $ \_ -> setCol left leftCol 
     right `onEvent` KeyUp $ \_ -> setCol right rightCol

     return ()
     
   _ -> alert $ "I'm missing some elements here! Make sure you have "
        ++ "'left', 'right', 'leftCol' and 'rightCol'!"

urlTable :: String -> [(Char, String)]
urlTable = (catMaybes . map tupIt . splitOn "&")
 where tupIt (l:'=':cs) = Just (l,cs)
       tupIt _          = Nothing 
   
setCol origin colBox = do
  Just text <- getValue origin
  case prettify text of
   Just text' -> setStyle colBox "backgroundColor" text'
   Nothing    -> return ()

prettify str@('#':xs) = if all isHex xs && length xs `elem` [3,6]
                        then Just str else Nothing 
  where isHex = (`elem` (['0'..'9'] ++ ['A'..'F'])) . toUpper
prettify str = prettify $ '#':str

urlHash :: IO String
urlHash = ffi "function() {return window.location.hash}"
