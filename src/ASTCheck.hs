{-# LANGUAGE FlexibleContexts #-}

{- | This module implements a means of turning a 'PreAST' into an
   'AST'.  In the process, the abstract syntax tree is checked for
   well-formedness. -}

module ASTCheck ( astOfPreAST ) where

import Control.Monad       ( foldM, when )
import Control.Monad.Except ( MonadError )
import Data.List           ( nub, intersect )
-- import Monad               ( when )

import AST
import ComputationMonad    ( ProgramError(..), abort )


{- ----------------------------------------------------------------------- -}
{- * Pre-AST translation and sanity checking -}

{- Returns the set of metavariable roots defined by the given list of
   declarations, raising an error instead if a root is defined
   multiple times. -}

getMvRoots :: (MonadError ProgramError m) => [MetavarDecl] -> m [MvRoot]
getMvRoots mvds = foldM f [] mvds
    where
      f acc (MetavarDecl pos rs _) =
          if not $ null $ intersect rs acc
          then abort $ ASTDupRoots pos (intersect rs acc)
          else return $ nub rs ++ acc

{- Returns the set of nonterminal roots defined by the given list of
   declarations, raising an error instead if a root is defined
   multiple times.  The given list of metavariable roots is used to
   check whether a root is defined both as a nonterminal and as a
   metavariable (an error). -}

getNtRoots :: (MonadError ProgramError m) => [MvRoot] -> [PreRule] -> m [MvRoot]
getNtRoots mvs rls = foldM f [] rls
    where
      f acc (Rule pos rs _ _) =
          if not $ null $ intersect rs (acc ++ mvs)
          then abort $ ASTDupRoots pos (intersect rs (acc ++ mvs))
          else return $ nub rs ++ acc

{- | Disambiguates the symbols in the given rule, in the process
   checking that the rule's productions are well-formed.  Binding
   specifications are checked only on a per-production basis.  Checks
   that require more \"global\" knowledge are not performed here.

   The supplied lists of roots are necessary in order to determine
   whether a symbol is a metavariable or a nonterminal. -}

toRule :: (MonadError ProgramError m) => [MvRoot] -> [NtRoot] -> PreRule -> m Rule
toRule mvs nts (Rule pos ns n ps) =
    do { ps' <- mapM toProduction ps
       ; return $ Rule pos ns n ps'
       }
    where
      toProduction (Production p es flag constr bs) =
          do { es'         <- foldM toElement [] es
             ; (_, _, bs') <- foldM (toBindingSpec es') ([], [], []) bs
             ; return $ Production p (reverse es') flag constr bs'
             }

      toElement acc (Unknown s) = return (acc ++ [TElement s])
      toElement acc (Variable v@(UnknownSym p r s))
          | r `elem` mvs && mv `notElem` acc = return (mv : acc)
          | r `elem` nts && nt `notElem` acc = return (nt : acc)
          | r `elem` mvs && mv `elem`    acc = abort  (ASTDupElt v)
          | r `elem` nts && nt `elem`    acc = abort  (ASTDupElt v)
          | otherwise                        = return (tm : acc)
          where
            mv = MvElement (Metavariable p r s)
            nt = NtElement (Nonterminal  p r s)
            tm = TElement  (r ++ s)

      toBindingSpec es (ls, rs, bss) (BindDecl p v1 v2) =
          do { v1' <- toMetavariable v1
             ; v2' <- toNonterminal  v2
             ; when (MvElement v1' `notElem` es) (abort $ ASTUnknownVar v1)
             ; when (NtElement v2' `notElem` es) (abort $ ASTUnknownVar v2)
             ; when (v1' `elem` ls) (abort $ ASTDupBinderL v1)
             ; when (v2' `elem` rs) (abort $ ASTDupBinderR v2)
             ; return $ (v1' : ls, v2' : rs, BindDecl p v1' v2' : bss)
             }

      toMetavariable x@(UnknownSym p r s)
          | r `elem` mvs = return $ Metavariable p r s
          | otherwise    = abort  $ ASTNotMv x

      toNonterminal x@(UnknownSym p r s)
          | r `elem` nts = return $ Nonterminal p r s
          | otherwise    = abort  $ ASTNotNt x


{- ----------------------------------------------------------------------- -}
{- * Exported functions -}

{- | Checks the abstract syntax tree for well-formedness and
   disambiguates the variables appearing in it.  Nonformal rules and
   metaproductions will be removed in the process. -}

astOfPreAST :: (MonadError ProgramError m) => PreAST -> m AST
astOfPreAST (PreAST mvds rls substs fvs) =
    do { mvs <- getMvRoots mvds
       ; nts <- getNtRoots mvs rls
       ; rs  <- mapM (toRule mvs nts) formalRules
       ; return $ AST mvds rs substs fvs
       }
    where
      formalRules = map deleteMetaprods $ filter isNonformal rls

      isNonformal (Rule _ es _ _) = "terminals" `notElem` es &&
                                    "formula"   `notElem` es

      deleteMetaprods (Rule pos es n ps) = Rule pos es n (filter f ps)
          where
            f (Production _ _ fs _ _) = null fs
