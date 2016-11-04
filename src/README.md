Caveats
=======

I try to keep the following information up to date, but sometimes I fall
a little  behind in  keeping track of  all the modifications  and design
decisions that I make while developing LNgen.


General implementation notes
============================

- I use the Monad Transformer Library for handling state and errors.
- There is one type for errors in the entire program.
- I usually keep type signatures as polymorphic as possible, even if
  this requires using a language extension, e.g., FlexibleContexts.


"Non-portable" libraries used
=============================

- Control.Monad.State
- Control.Monad.Error
- Data.Generics


Language extensions used
========================

- DeriveDataTypeable
- FlexibleContexts


Dataflow through various files
==============================

The   `Main`   module  ties   everything   together.    The  `AST`   and
`ComputationMonad` modules more or less cut across everything.

    Parser ( parseOttFile )
      |
      | PreAST
      |
      v                         AST
    ASTCheck ( astOfPreAST ) ---------> ASTAnalysis ( analyzeAST )
      |                                    /
      | AST                               /
      |                                  / ASTAnalysis
      v                                 /
    CoqLNOutput ( coqOfAST ) <---------+
      |
      | String
      |
      v
    [final output]

Dependencies
============
- [Parsec](https://hackage.haskell.org/package/parsec)
- [SYB](http://hackage.haskell.org/package/syb)

You can fulfill the dependencies with `cabal install parsec syb`.
