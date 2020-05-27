{- | This module defines a library of assorted functions that I have
   not found in (GHC's) standard library. -}

module MyLibrary where

import Data.List  ( intercalate, nub, minimumBy )
import Data.Map   ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import Text.ParserCombinators.Parsec ( GenParser, manyTill )
import Control.Monad.Fail as Fail


{- ----------------------------------------------------------------------- -}
{- * General purpose parsing combinators -}

{- | A variant of the 'manyTill' combinator that requires that the
   first argument succeed at least once. -}

manyTill1 :: GenParser tok st t ->
             GenParser tok st end ->
             GenParser tok st [t]
manyTill1 p end =
    do { x <- p
       ; xs <- p `manyTill` end
       ; return (x:xs)
       }


{- ----------------------------------------------------------------------- -}
{- * Error handling -}

{- | Views 'Either' as an error monad and returns the result of the
   computation or else calls 'error'. -}

getResult :: Show a => Either a b -> b
getResult (Right res) = res
getResult (Left err)  = error (show err)


{- ----------------------------------------------------------------------- -}
{- * Miscellaneous functions -}

{- | A variant of 'Map.lookup' that either @return@s its result in the
   given monad or @fail@s. -}

mapLookup :: (MonadFail m, Ord k, Show k) => k -> Map k a -> m a
mapLookup k m = case Map.lookup k m of
                  Just x  -> return x
                  Nothing -> Fail.fail $ "mapLookup: " ++ show k ++
                                    " not found in: " ++ show (Map.keys m)

{- | A variant on 'mapM' for when the function returns as a 'Maybe' value. -}

mapMM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMM f as =
    do { bs <- mapM f as
       ; return $ catMaybes bs
       }

{- | Shorthand for @nub . map f@. -}

nmap :: Eq b => (a -> b) -> [a] -> [b]
nmap f = nub . map f

{- | Concatenates the result of interspersing the first argument
   between the elements of the second argument. -}

sepStrings :: String -> [String] -> String
sepStrings = intercalate

{- | Returns the shortest string in the given list.  Ties are broken
   by choosing the string that appears first in the input.  The input
   list must be non-empty. -}

shortestStr :: [String] -> String
shortestStr = minimumBy (\x y -> compare (length x) (length y))
