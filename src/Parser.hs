{- | This module defines the functions necessary to parse an Ott input
   file and check that it is well formed.

   Implementation notes (BEA):

   1. The comments below assume some level of familiarity with Parsec.

   2. Parsers below are implemented assuming that they don't need to
      consume any initial whitespace.  This means that they all need
      to be implemented as lexeme parsers, ones that consume trailing
      whitespace.  A few parsers are not lexeme parsers; these are
      noted below.
-}

module Parser ( parseOttFile ) where

import Data.Maybe ( catMaybes )
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language ( emptyDef )
import qualified Text.ParserCombinators.Parsec.Token as P
import Data.List.NonEmpty as NE

import AST
import MyLibrary ( getResult, manyTill1 )


{- ----------------------------------------------------------------------- -}
{- * Basic, language specific parsers -}

{- | A parser \"module\" used mainly for handling whitespace,
   comments, and reserved words in Ott input files. -}

ottTokenParser :: P.TokenParser st
ottTokenParser = P.makeTokenParser (emptyDef { P.commentLine = "%" })

{- | A parser for whitespace, including comments. -}

whiteSpace :: CharParser st ()
whiteSpace = P.whiteSpace ottTokenParser

{- | Constructs a lexeme parser from its argument. -}

lexeme :: CharParser st a -> CharParser st a
lexeme = P.lexeme ottTokenParser

{- | A lexeme parser for identifiers. -}

identifier :: CharParser st String
identifier = P.identifier ottTokenParser

{- | A lexeme parser for reserved words. -}

reserved :: String -> CharParser st ()
reserved = P.reserved ottTokenParser

{- | A lexeme parser that is otherwise similar to the 'string' parser.
   It does not consume any input on failure. -}

text :: String -> CharParser st String
text str = lexeme $ try $ string str


{- | sepBy1, but produce a nonempty list of results -}
ne_sepBy1 :: Parser a1 -> Parser a2 -> Parser (NonEmpty a1)
ne_sepBy1 p sep        = do{ x <- p
                        ; xs <- many (sep >> p)
                        ; return (x :| xs)
                        }

{- ----------------------------------------------------------------------- -}
{- * Parsing names -}

{- | A variable (e.g., metavariable, nonterminal, etc.) consists of a
   root and suffix followed by at least one whitespace character. -}

var :: Parser UnknownSym
var = lexeme $ do { pos <- getPosition
                  ; r   <- root
                  ; s   <- suffix
                  ; _   <- space
                  ; return $ UnknownSym pos r s
                  }

{- | The root of a variable consists of a non-empty sequence of
   letters and underscores.  This is NOT a lexeme parser. -}

root :: Parser Root
root = many1 ((letter <|> char '_') <?> "") <?> "name"

{- | A suffix of a variable is a (possibly empty) sequence of digits
   and primes.  This is NOT a lexeme parser. -}

suffix :: Parser Suffix
suffix = many (digit <|> char '\'')

{- | 'name' is a lexeme parser version of 'root'. -}

name :: Parser Root
name = lexeme root

{- | 'nameHom' is a version of 'name' that consumes all trailing
   homomorphisms. -}

nameHom :: Parser Root
nameHom = do { n <- name ; ignoreHoms ; return n }


{- ----------------------------------------------------------------------- -}
{- * Ignoring homomorphisms -}

{- | Consumes a homomorphism from the input stream. -}

ruleHom :: Parser RuleHom
ruleHom =
    do { _ <- text "{{" <?> "homomorphism \"{{ ... }}\""
             ; do { reserved "phantom"
                  ; _ <- text "}}"
                  ; return RuleHom {ruleHomPhantom = True}
                  }
               <|>
               mempty <$ anyChar `manyTill` text "}}"
             }

ignoreHom :: Parser ()
ignoreHom =
    do { _ <- text "{{" <?> "homomorphism \"{{ ... }}\""
       ; _ <- anyChar `manyTill` text "}}"
       ; return ()
       }

{- | Consumes zero or more homomorphisms from the input stream. -}

ignoreHoms :: Parser ()
ignoreHoms = do { _ <- many ignoreHom ; return () }


{- ----------------------------------------------------------------------- -}
{- * Parsing metavariable declarations -}

{- | A metavariable declaration consists of a non-empty list of
   metavariable roots and a possibly empty list of homomorphisms -}




metavarDecl :: Parser MetavarDecl
metavarDecl =
    do { pos <- getPosition
       ; reserved "metavar" <?> "metavariable declaration \"metavar ...\""
       ; names <- nameHom `ne_sepBy1` (text "," <?> "\",\" and another name")
       ; _ <- text "::="
       ; homs <- many metavarHom
       ; return (MetavarDecl pos names (NE.prependList (catMaybes homs) defaults))
       }
    where
      defaults = CoqMvImplHom "atom" :| []

      metavarHom =
          do { _ <- text "{{" <?> "homomorphism \"{{ ... }}\""
             ; do { reserved "phantom"
                  ; _ <- text "}}"
                  ; return $ Just $ MvPhantom
                  }
               <|>
               do { _ <- anyChar `manyTill` text "}}"
                  ; return Nothing
                  }
             }

{- ----------------------------------------------------------------------- -}
{- * Parsing definitions of nonterminals -}

{- | A rule defines a nonterminal.  The definition begins with a list
   of roots, followed by a name and homomorphisms.  The remainder of
   the rule is a sequence of productions. -}

rule :: Parser PreRule
rule =
    do { pos <- getPosition
       ; es <- nameHom `ne_sepBy1` (text "," <?> "\",\" and another name")
       ; _ <- text "::"
       ; n <- ruleName
       ; _ <- text "::="
       ; hom <- mconcat <$> many ruleHom
       ; prods <- many production
       ; return $ Rule pos hom es n prods
       }
    where
      ruleName =
          lexeme (try (many1 (letter <|> char '_' <?> "")) <?> "name")
          <|>
          -- BEA: Seems like unnecessary flexbility in the input language.
          lexeme (do { _ <- char '\''
                     ; (letter <|> char '_') `manyTill` char '\''
                     })

{- | Each production in a rule starts with a \"|\" followed by a
   non-empty sequence of elements.  This is followed by flags, a name
   for this production, binding specifications, and homomorphisms. -}

production :: Parser PreProduction
production =
    do { pos <- getPosition
       ; _ <- text "|"
       ; es <- element `manyTill` text "::"
       ; flag <- many productionFlag
       ; _ <- text "::"
       ; constr <- identifier
       ; bs <- many bindingSpec
       ; _  <- many ignoreHom
       ; return $ Production pos es flag constr bs
       }
    where
      productionFlag =
          do { reserved "I"; return IFlag }
          <|>
          do { reserved "M"; return MFlag }
          <|>
          do { reserved "S"; return SFlag }

{- | An element is a terminal, nonterminal, or metavariable.

   Implementation note (BEA): The difference between these three is
   sorted out later since we don't have enough information at this
   stage to make this distinction.  We are careful to identify
   potential nonterminals and metavariables as such. -}

element :: Parser UnknownElement
element =
    try (do { v <- var
            ; return $ Variable v
            })
    <|>
    try (do { s <- noneOf " \v\f\t\r\n" `manyTill1` whiteSpace
            ; return $ Unknown s
            })

{- | A binding specification helps define the binding structure of a
   given production.  Similar to 'element', we sort out references to
   variables later. -}

bindingSpec :: Parser PreBindingSpec
bindingSpec =
    do { pos <- getPosition
       ; _ <- text "(+"
       ; b <- do { reserved "bind"
                 ; v1 <- var
                 ; reserved "in"
                 ; v2 <- var
                 ; return $ BindDecl pos v1 v2
                 }
       ; _ <- text "+)"
       ; return b
       }


{- ----------------------------------------------------------------------- -}
{- * Function names -}

{- | Parses a @substitutions@ block. -}

substitutions :: Parser [SubstFun]
substitutions =
    do { reserved "substitutions"
       ; many (try substitution)
       }
    where
      substitution =
          do { reserved "single"
             ; nt <- name
             ; mv <- name
             ; _ <- text "::"
             ; n <- name
             ; return $ SingleSubstFun nt mv n
             }

{- | Parses a @freevars@ block. -}

freevars :: Parser [FvFun]
freevars =
    do { reserved "freevars"
       ; many (try freevar)
       }
    where
      freevar =
          do { nt <- name
             ; mv <- name
             ; _ <- text "::"
             ; n <- name
             ; return $ FvFun nt mv n
             }


{- ----------------------------------------------------------------------- -}
{- * Ignoring Ott code -}

indexVarDecl :: Parser ()
indexVarDecl =
    do { reserved "indexvar" <?> "indexvar declaration \"indexvar ...\""
       ; _ <- nameHom `sepBy1` (text "," <?> "\",\" and another name")
       ; _ <- text "::="
       ; _ <- many ignoreHom
       ; return ()
       }

embed :: Parser ()
embed =
    do { reserved "embed"
       ; _ <- many ignoreHom
       ; return ()
       }

ignoreBlocks :: Parser ()
ignoreBlocks =
    do { _ <- many (indexVarDecl <|> embed)
       ; return ()
       }


{- ----------------------------------------------------------------------- -}
{- * Parsing an entire file -}

{- | A parser for an entire Ott file. -}

ottFileParser :: Parser PreAST
ottFileParser = do { whiteSpace
                   ; ignoreBlocks
                   ; mvds <- many metavarDecl
                   ; ignoreBlocks
                   ; reserved "grammar"
                   ; rs <- many (try rule)
                   ; ignoreBlocks
                   ; substs <- option [] substitutions
                   ; ignoreBlocks
                   ; fvs <- option [] freevars
                   -- ; BEA: Really rough debugging code.
                   -- ; pos <- getPosition
                   -- ; let x = unsafePerformIO (putStrLn (show pos))
                   -- ; case x of () -> return ()
                   ; return $ PreAST mvds rs substs fvs
                   }

{- | Parses an entire Ott file given its name. -}

parseOttFile :: String -> IO PreAST
parseOttFile filename =
    do { answer <- parseFromFile ottFileParser filename
       ; return (getResult answer)
       }
