{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{- | This module implements the errors and monads that are used to
   structure many of the computations in this program. -}

module ComputationMonad where

import Control.Monad.Except
import Control.Monad.Fail()
import Control.Monad.State
import Data.Map ( Map )
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec ( SourcePos )

import AST
import MyLibrary ( getResult, sepStrings )


{- ----------------------------------------------------------------------- -}
{- * \"Global state\" -}

{- | Datatype for command-line flags. -}

data ProgFlag
    = CoqAdmitted        -- ^ Do not generate proofs.
    | CoqLoadPath String -- ^ The path component of the LoadPath declaration.
    | CoqOtt String      -- ^ Name of the library to @Require@ in generated output.
    | CoqOutput String   -- ^ Destination for output.
    | CoqStdout          -- ^ Send output to standard out.
    | CoqNoLCSet         -- ^ Suppress the Set version of Local Closure.
    | CoqNoClose         -- ^ Suppress generation of close and close_rec.
    | Help               -- ^ Display usage information.
    deriving ( Eq )


{- ----------------------------------------------------------------------- -}
{- * Errors -}

{- | This is the datatype for all errors that might be generated in
   the course of this program's execution.  The 'Show' instance for
   the datatype defines the meaning of the errors.  They are all fatal
   errors, in the sense that there are no guarantees about the
   validity of any proof assistant output that might be output from
   this program. -}

data ProgramError
    -- Errors encountered while traversing an AST or PreAST.
    = ASTDupBinderL  UnknownSym
    | ASTDupBinderR  UnknownSym
    | ASTDupElt      UnknownSym
    | ASTDupRoots    SourcePos [Root]
    | ASTNotMv       UnknownSym
    | ASTNotNt       UnknownSym
    | ASTUnknownVar  UnknownSym

    -- Errors encountered during AST analysis.
    | AmbiguousMvSort  SourcePos MvRoot [NtRoot]
    | NoMvSort         SourcePos MvRoot
    | NonBindingMv     SourcePos

    -- An unknown, or generic, error.
    | GenericError String

instance Show ProgramError where
    -- Errors encountered during AST sanity checking.
    show (ASTDupBinderL v)    = toPosS v ++ ": " ++ show v ++ " already binds in something"
    show (ASTDupBinderR v)    = toPosS v ++ ": " ++ show v ++ " already has a binder"
    show (ASTDupElt v)        = toPosS v ++ ": " ++ show v ++ " is already defined in this production"
    show (ASTDupRoots pos rs) = show pos ++ ": " ++ (sepStrings ", " rs) ++ " is/are already defined"
    show (ASTNotMv v)         = toPosS v ++ ": " ++ show v ++ " is not a metavariable"
    show (ASTNotNt v)         = toPosS v ++ ": " ++ show v ++ " is not a nonterminal"
    show (ASTUnknownVar v)    = toPosS v ++ ": " ++ show v ++ " is not in scope"

    -- Errors encountered during AST analysis.
    show (AmbiguousMvSort pos mv nts) = show pos ++ ": Ambiguous type for " ++ show mv ++ ": " ++ sepStrings ", " nts ++ "."
    show (NoMvSort pos mv)            = show pos ++ ": No discernable type for " ++ show mv ++ "."
    show (NonBindingMv pos)           = show pos ++ ": Production has a non-binding metavariable."

    -- An unknown, or generic, error.
    show (GenericError s) = "Error: " ++ s


{- ----------------------------------------------------------------------- -}
{- * Combining error and state -}

{- | The following monad allows to program in the presence of errors
   ('ProgramError') while maintaining state.  The idea is that
   generated names take the form \"root + integer suffix\".  The map
   in the state keeps track of the most recent suffix that was handed
   out. -}

newtype M a = M { getM :: ExceptT ProgramError (State ([ProgFlag], Map String Int)) a }
   deriving (Functor, Applicative, Monad, MonadError ProgramError, MonadState ([ProgFlag], Map String Int))


instance MonadFail M where
   fail s = throwError (GenericError s)

{- | Runs a computation that lives in 'M'. -}

runM :: [ProgFlag] -> M a -> a
runM flags =
    getResult . fst . flip runState (flags, Map.empty) . runExceptT . getM

{- | Another name for 'throwError'. -}

abort :: (MonadError e m) => e -> m a
abort = throwError

{- | Saves the current state, does the given computation, and then
   restores the saved state.  The result returned is that of the given
   computation.  'M' is a suitable monad here. -}

local :: (MonadState s m) => m a -> m a
local comp =
    do { s <- get
       ; res <- comp
       ; put s
       ; return res
       }

{- | Computes a new name with the given root string.  'M' is a
   suitable monad here. -}

newName :: (Show t, Num t, MonadState (b, Map String t) m) => String -> m String
newName r =
    do { (b, m) <- get
       ; let i = Map.findWithDefault 1 r m
       ; put (b, Map.insert r (i+1) m)
       ; return $ r ++ show i
       }

{- | Reset the map so that it is empty.  'M' is a suitable monad here.
   With respect to fresh name generation, it will be as if no names
   have ever been generated. -}

reset :: (MonadState (b, Map k a) m) => m ()
reset =
    do { (b, _) <- get
       ; put (b, Map.empty)
       }

{- | Check whether to not generate lc set  -}
nolcset :: [ProgFlag] -> Bool
nolcset = elem CoqNoLCSet

{- | Check whether to not generate close  -}
noclose :: [ProgFlag] -> Bool
noclose = elem CoqNoClose
