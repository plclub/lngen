{- | This module defines the @main@ IO action for this program. -}

module Main where

import Control.Monad      ( when )
import System.Environment  ( getArgs, getProgName )
import System.IO       ( hPutStr, stderr, stdout )
import System.Console.GetOpt
import Text.Printf     ( printf )

import ASTCheck         ( astOfPreAST )
import ComputationMonad ( runM, ProgFlag(..) )
import CoqLNOutput      ( coqOfAST )
import MyLibrary        ( getResult )
import Parser           ( parseOttFile )


{- ----------------------------------------------------------------------- -}
{- * Constants -}

{- | LNgen's version number. -}

version :: String
version = "0.3.2"


{- ----------------------------------------------------------------------- -}
{- * Parsing command-line arguments -}

{- | The usage message for this program.  It depends on the name this
   program was invoked by. -}

usageMsg :: IO String
usageMsg = do { n <- getProgName
              ; return (usageInfo
                        (printf "Usage: %s [OPTION1 OPTION2 ...] FILE1\n" n)
                        options)
              }

{- | Command-line options. -}

options :: [OptDescr ProgFlag]
options =
    [ Option ['o'] ["coq"]           (ReqArg CoqOutput "FILE")  "Coq: destination for output"
    , Option []    ["coq-admitted"]  (NoArg CoqAdmitted)        "Coq: do not generate proofs"
    , Option []    ["coq-no-proofs"] (NoArg CoqAdmitted)        "Coq: do not generate proofs"
    , Option []    ["coq-loadpath"]  (ReqArg CoqLoadPath "DIR") "Coq: directory for LoadPath"
    , Option []    ["coq-ott"]       (ReqArg CoqOtt "LIB")      "Coq: name of library to Require"
    , Option []    ["coq-stdout"]    (NoArg CoqStdout)          "Coq: send output to standard out"
    , Option []    ["coq-nolcset"]   (NoArg CoqNoLCSet)         "Coq: suppress the Set version of local closure"
    , Option ['?'] ["help"]          (NoArg Help)               "displays usage information"
    ]

{- | Processes the command-line arguments to this program.  Returns a
   list of flags and a list of non-options. -}

processArgv :: IO ([ProgFlag], [String])
processArgv =
    do { argv   <- getArgs
       ; usage  <- usageMsg
       ; (o, n) <- case getOpt Permute options argv of
                     (o, n, []) -> return (o, n)
                     (_, _, es) -> error $ concat es ++ "\n" ++ usage
       ; when (Help `elem` o) (error usage)
       ; when (length n /= 1) (error $ "Exactly one input file required.\n\n" ++ usage)
       ; return (o, n)
       }


{- ----------------------------------------------------------------------- -}
{- * The \"main\" action -}

{- | Returns the content of the @--coq-loadpath@ option, if any. -}

getCoqLoadPath :: [ProgFlag] -> Maybe String
getCoqLoadPath []                  = Nothing
getCoqLoadPath (CoqLoadPath s : _) = Just s
getCoqLoadPath (_ : flags)         = getCoqLoadPath flags

{- | Returns the content of the @--coq-ott@ option, if any -}

getCoqOtt :: [ProgFlag] -> Maybe String
getCoqOtt []             = Nothing
getCoqOtt (CoqOtt s : _) = Just s
getCoqOtt (_ : flags)    = getCoqOtt flags

{- | The main action for this program. -}

main :: IO ()
main =
    do { hPutStr stderr (printf "This is version %s of LNgen.\n\n" version)
       ; (flags, inputNames) <- processArgv
       ; mapM_ (processInput flags) inputNames
       }
    where
      processInput flags file =
          do { preAst <- parseOttFile file
             ; let ast       = getResult (astOfPreAST preAst)
                   ott       = getCoqOtt flags
                   loadpath  = getCoqLoadPath flags
                   coqOutput = runM flags $ coqOfAST ott loadpath ast
             ; mapM_ (output $! coqOutput) flags
             }

      output coq (CoqOutput f) = writeFile f coq
      output coq (CoqStdout)   = hPutStr stdout coq
      output _   _             = return ()
