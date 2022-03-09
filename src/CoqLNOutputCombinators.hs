{- | This module defines a collection of combinators for looping over
   nonterminals and metavariables, as well as for assembling output
   for Coq. -}

module CoqLNOutputCombinators where

import Control.Monad.State
import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import MyLibrary ( sepStrings )


{- ----------------------------------------------------------------------- -}
{- * Generating text for lemmas -}

{- Flag for Coq's sorts. -}

data Sort = Prop | Set

instance Show Sort where
    show Prop = "Prop"
    show Set  = "Set"

{- Flag indicating what sort of @Resolve@ hint to generate. -}

data ResolveHint = NoResolve | Resolve | Immediate

{- Flag indicating what sort of @Rewrite@ hint to generate. -}

data RewriteHint = NoRewrite | Rewrite

{- Flag indicating whether to generate @hide@ directives for @coqdoc@. -}

data DocHide = NoHide | Hide

{- Basic combinator for generating the text of a lemma declaration. -}

lemmaText :: ResolveHint -- Resolve hint?
          -> RewriteHint -- Rewrite hint?
          -> DocHide     -- Hide documentation?
          -> [String]    -- Hint databases.
          -> String      -- Name of the lemma
          -> String      -- Statment of the lemma
          -> String      -- Proof of the lemma
          -> M String
lemmaText resolve rewrite hide dbs name stmt proof =
    do { (flags, _) <- get
       ; return $ printf "%s\
                         \Lemma %s :\n\
                         \%s.\n\
                         \%s\
                         \%s%s%s%s"
         (case hide of
            NoHide -> ""
            Hide   -> "(* begin hide *)\n\n")
         name
         stmt
         (if CoqAdmitted `elem` flags
          then "Proof. Admitted.\n\n"
          else printf "Proof.\n\
                      \%s\n\
                      \Qed.\n\
                      \\n"
                      proof)
         (case resolve of
            NoResolve -> ""
            Resolve   -> printf "#[export] Hint Resolve %s : %s.\n" name (sepStrings " " dbs)
            Immediate -> printf "#[export] Hint Immediate %s : %s.\n" name (sepStrings " " dbs))
         (case rewrite of
            NoRewrite -> ""
            Rewrite   -> printf "#[export] Hint Rewrite %s using solve [auto] : %s.\n" name (sepStrings " " dbs))
         (case (resolve, rewrite) of
            (NoResolve, NoRewrite) -> ""
            _ -> "\n")
         (case hide of
            NoHide -> ""
            Hide   -> "(* end hide *)\n\n")
       }

{- Basic combinator for generating the text of a lemma declaration. -}

lemmaText2 :: ResolveHint          -- Resolve hint?
           -> RewriteHint          -- Rewrite hint?
           -> DocHide              -- Hide documentation?
           -> [String]             -- Hint databases.
           -> [[String]]           -- Names for the parts.
           -> [[(String, String)]] -- Statments and proofs for the parts.
           -> M String
lemmaText2 resolve rewrite hide dbs names gens =
    do { strs <- mapM (\(name, (stmt, pf)) ->
                           lemmaText resolve rewrite hide dbs name stmt pf)
                      (zip (concat names) (concat gens))
       ; return $ concat strs
       }

{- Combinator used for generating the text of a lemma proved by mutual
   induction/recursion. -}

mutualLemmaText :: ResolveHint -- Resolve hint?
                -> RewriteHint -- Rewrite hint?
                -> DocHide     -- Hide documentation?
                -> [String]    -- Hint databases.
                -> Sort        -- Sort
                -> [String]    -- Names for the parts.
                -> [String]    -- Statments for the parts.
                -> String      -- Proof of the lemma.
                -> M String
mutualLemmaText resolve rewrite hide dbs sort names stmts proof =
    do { let mut_name  = sepStrings "_" names ++ "_mutual"
             mut_stmts = combine sort $ map wrap stmts
             cproof      = printf "pose proof %s as H; intuition eauto." mut_name
       ; lemma <- lemmaText NoResolve NoRewrite Hide dbs mut_name mut_stmts proof
       ; corollaries <- mapM (\(name, stmt) ->
                                  lemmaText resolve rewrite hide dbs name stmt cproof)
                             (zip names stmts)
       ; return $ lemma ++ concat corollaries
       }
    where
      combine Set  = sepStrings " *\n"
      combine Prop = sepStrings " /\\\n"
      wrap str     = printf "(%s)" str

{- Combinator used for generating the text of a lemma proved by mutual
   induction/recursion. -}

mutualLemmaText2 :: ResolveHint -- Resolve hint?
                 -> RewriteHint -- Rewrite hint?
                 -> DocHide     -- Hide documentation?
                 -> [String]    -- Hint databases.
                 -> Sort        -- Sort
                 -> [[String]]  -- Names for the parts.
                 -> [[String]]  -- Statments for the parts.
                 -> [String]    -- Proof of the lemma.
                 -> M String
mutualLemmaText2 resolve rewrite hide dbs sort names stmts proof =
    do { strs <- mapM (\(name, stmt, pf) ->
                           mutualLemmaText resolve rewrite hide dbs sort name stmt pf)
                      (zip3 names stmts proof)
       ; return $ concat strs
       }

{- Combinator used to generate the application of the mutual
   induction/recursion principle. -}

mutPfStart :: Sort
           -> [Name]    -- Names of types.
           -> String
mutPfStart s ns = f (case s of { Prop -> mutIndName ; Set -> mutRecName })
    where
      f g = printf "%s %s;\n" applyMutInd (g ns)


{- ----------------------------------------------------------------------- -}
{- * Looping patterns -}

{- Combinator used to loop over a set of @nt1s@. -}

processNt1 :: ASTAnalysis
           -> [NtRoot]
           -> (ASTAnalysis -> NtRoot -> M a)
           -> M [a]
processNt1 aa nt1s f = mapM (local . f aa) nt1s

{- Combinator used to loop over @(nt1, nt2, mv2)@ triples. -}

processNt1Nt2Mv2 :: ASTAnalysis
                 -> [NtRoot]
                 -> (ASTAnalysis -> NtRoot -> NtRoot -> MvRoot -> M a)
                 -> M [[a]]
processNt1Nt2Mv2 aa nt1s f =
    sequence $
    do { nt2 <- filter (canBindOver aa (head nt1s)) (ntRoots aa)
       ; mv2 <- mvsOfNt aa nt2
       ; return $ sequence $ do { nt1 <- nt1s
                                ; return (local $ f aa nt1 nt2 mv2)
                                }
       }

{- Combinator used to loop over @(nt1, nt2, mv2, nt2', mv2')@ tuples. -}

processNt1Nt2Mv2' :: ASTAnalysis
                  -> [NtRoot]
                  -> (ASTAnalysis -> NtRoot -> NtRoot -> MvRoot -> NtRoot -> MvRoot -> M a)
                  -> M [[a]]
processNt1Nt2Mv2' aa nt1s f =
    sequence $
    do { nt2  <- filter (canBindOver aa (head nt1s)) (ntRoots aa)
       ; mv2  <- mvsOfNt aa nt2
       ; nt2' <- filter (canBindOver aa (head nt1s)) (ntRoots aa)
       ; mv2' <- mvsOfNt aa nt2'
       ; return $ sequence $ do { nt1 <- nt1s
                                ; return (local $ f aa nt1 nt2 mv2 nt2' mv2')
                                }
       }
