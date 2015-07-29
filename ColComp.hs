{-# LANGUAGE OverloadedStrings #-}
import Haste.Events
import Haste.DOM
import Haste.Foreign
import Haste

import Data.Char (toUpper, toLower)
import Data.List.Split (splitOn)
import Data.List
import Data.Maybe (catMaybes)

import Debug.Trace

main = do
  url <- urlHash
  let (l, r) = getLR url
  elems <- mapM elemById ["left", "right", "leftCol", "rightCol"]
  
  case catMaybes elems of
   [left, right, leftCol, rightCol] -> do
     case prettify l of
      Just str -> setProp left "value" str
      _        -> setProp left "value" "#FFFFFF"
     case prettify r of
      Just str -> setProp right "value" str
      _        -> setProp right "value" "#000000"

     setCol left leftCol
     left `onEvent` KeyUp $ \_ -> setCol left leftCol 
     setCol right rightCol
     right `onEvent` KeyUp $ \_ -> setCol right rightCol
     return ()
     
   _ -> alert $ "I'm missing some elements here! Make sure you have "
        ++ "'left', 'right', 'leftCol' and 'rightCol'!"

getLR :: String -> (String, String)
getLR xs = let list = (catMaybes . map tupIt . splitOn "&") xs
           in (getStr 'l' list, getStr 'r' list)
  where tupIt (c:'=':cs) = Just (c,cs)
        tupIt _          = Nothing
        getStr c = snd . head . filter ((== c) . fst)
   
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
