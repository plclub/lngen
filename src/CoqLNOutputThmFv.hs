{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -freduction-depth=50 #-}

module CoqLNOutputThmFv where

import Data.Maybe  ( catMaybes )
import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators

fvThms :: ASTAnalysis -> [[NtRoot]] -> M String
fvThms aa nts =
    do { fv_close_recs      <- mapM (local . fv_close_rec aa) nts
       ; fv_closes          <- mapM (local . fv_close aa) nts
       ; fv_open_lower_recs <- mapM (local . fv_open_lower_rec aa) nts
       ; fv_open_lowers     <- mapM (local . fv_open_lower aa) nts
       ; fv_open_upper_recs <- mapM (local . fv_open_upper_rec aa) nts
       ; fv_open_uppers     <- mapM (local . fv_open_upper aa) nts
       ; fv_subst_freshs    <- mapM (local . fv_subst_fresh aa) nts
       ; fv_subst_lowers    <- mapM (local . fv_subst_lower aa) nts
       ; fv_subst_notins    <- mapM (local . fv_subst_notin aa) nts
       ; fv_subst_uppers    <- mapM (local . fv_subst_upper aa) nts
       ; return $ printf "Ltac %s ::= auto with set %s; tauto.\n\
                         \Ltac %s ::= autorewrite with %s.\n\
                         \\n"
                         defaultAuto hintDb
                         defaultAutoRewr hintDb ++
                  concat fv_close_recs ++
                  concat fv_closes ++
                  concat fv_open_lower_recs ++
                  concat fv_open_lowers ++
                  concat fv_open_upper_recs ++
                  concat fv_open_uppers ++
                  concat fv_subst_freshs ++
                  concat fv_subst_lowers ++
                  concat fv_subst_notins ++
                  concat fv_subst_uppers ++ "\n"
       }

{- | @fv (close_rec n x e) [=] remove x (fv e)@. -}

fv_close_rec :: ASTAnalysis -> [NtRoot] -> M String
fv_close_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let proof = map head proofs
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      pf _ _ _ _ _ _ =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ mutPfStart Prop types ++
                        defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn <- fvName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ close_fn
             }

      thm aa nt1 _ mv2 _ mv2' | mv2 == mv2' =
          do { k        <- newName bvarRoot
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [=] %s %s (%s %s)"
                        e x k
                        fv_fn close_fn k x e mvSetRemove x fv_fn e
             }

      thm aa nt1 _ mv2 _ mv2' | otherwise =
          do { k        <- newName bvarRoot
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [=] %s %s"
                        e x k
                        fv_fn close_fn k x e fv_fn e
             }

{- | @fv (close x e) [=] remove x (fv e)@. -}

fv_close :: ASTAnalysis -> [NtRoot] -> M String
fv_close aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn <- fvName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ close_fn
             }

      gen aa nt1 _ mv2 _ mv2' | mv2 == mv2' =
          do { e        <- newName nt1
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s (%s %s %s) [=] %s %s (%s %s)"
                                 e x
                                 fv_fn close_fn x e mvSetRemove x fv_fn e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

      gen aa nt1 _ mv2 _ mv2' | otherwise =
          do { e        <- newName nt1
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s (%s %s %s) [=] %s %s"
                                 e x
                                 fv_fn close_fn x e fv_fn e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @fv e [<=] fv (open_rec k e' e)@. -}

fv_open_lower_rec :: ASTAnalysis -> [NtRoot] -> M String
fv_open_lower_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let proof = map head proofs
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      pf _ _ _ _ _ _ =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ mutPfStart Prop types ++
                        defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn <- fvName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ open_fn ++ "_lower"
             }

      thm aa nt1 _ mv2 nt2' mv2' =
          do { k       <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; fv_fn   <- fvName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s [<=] %s (%s %s %s %s)"
                        e u k
                        fv_fn e fv_fn open_fn k u e
             }

{- | @fv e [<=] fv (open e e')@. -}

fv_open_lower :: ASTAnalysis -> [NtRoot] -> M String
fv_open_lower aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn <- fvName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ open_fn ++ "_lower"
             }

      gen aa nt1 _ mv2 nt2' mv2' =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; fv_fn   <- fvName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s [<=] %s (%s %s %s)"
                                 e u
                                 fv_fn e fv_fn open_fn e u
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @fv (open_rec n e' e) [<=] fv e' `union` fv e@. -}

fv_open_upper_rec :: ASTAnalysis -> [NtRoot] -> M String
fv_open_upper_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let proof = map head proofs
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      pf _ _ _ _ _ _ =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ mutPfStart Prop types ++
                        defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn <- fvName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ open_fn ++ "_upper"
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { k       <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; open_fn <- openRecName aa nt1 mv2'
             ; fv_fn   <- fvName aa nt1 mv2
             ; fv_fn2  <- fvName aa nt2' mv2
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [<=] %s %s %s %s %s"
                        e u k
                        fv_fn open_fn k u e fv_fn2 u mvSetUnion fv_fn e
             }

      thm aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { k       <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; open_fn <- openRecName aa nt1 mv2'
             ; fv_fn   <- fvName aa nt1 mv2
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [<=] %s %s"
                        e u k
                        fv_fn open_fn k u e fv_fn e
             }

{- | @fv (open e e') [<=] fv e `union` fv e'@. -}

fv_open_upper :: ASTAnalysis -> [NtRoot] -> M String
fv_open_upper aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn <- fvName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ open_fn ++ "_upper"
             }

      gen aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; open_fn <- openName aa nt1 mv2'
             ; fv_fn   <- fvName aa nt1 mv2
             ; fv_fn2  <- fvName aa nt2' mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                               \  %s (%s %s %s) [<=] %s %s %s %s %s"
                        e u
                        fv_fn open_fn e u fv_fn2 u mvSetUnion fv_fn e
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

      gen aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; open_fn <- openName aa nt1 mv2'
             ; fv_fn   <- fvName aa nt1 mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                               \  %s (%s %s %s) [<=] %s %s"
                        e u
                        fv_fn open_fn e u fv_fn e
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @x `notin` fv e -> fv (subst e' x e) [=] fv e@. -}

fv_subst_fresh :: ASTAnalysis -> [NtRoot] -> M String
fv_subst_fresh aaa nt1s =
    do { thms'     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names'    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs'   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let thms   = filter (not . null) $ map catMaybes thms'
       ; let names  = filter (not . null) $ map catMaybes names'
       ; let proofs = filter (not . null) $ map catMaybes proofs'
       ; let proof  = map head proofs
       ; mutualLemmaText2 Resolve Rewrite NoHide [hintDb] Prop names thms proof
       }
    where
      pf aa _ nt2 mv2 nt2' mv2' | mv2 == mv2' || not (canBindIn aa nt2 nt2')  =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ Just $ mutPfStart Prop types ++
                               defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      pf _ _ _ _ _ _ | otherwise = return Nothing

      name aa nt1 nt2' mv2 nt2 mv2' | mv2 == mv2' || not (canBindIn aa nt2 nt2') =
          do { fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ Just $ fv_fn ++ "_" ++ subst_fn ++ "_fresh"
             }

      name _ _ _ _ _ _ | otherwise = return Nothing

      thm aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ Just $ printf "forall %s %s %s,\n\
                                      \  %s %s %s %s ->\n\
                                      \  %s (%s %s %s %s) [=] %s %s"
                                      e u x
                                      x mvSetNotin fv_fn e
                                      fv_fn subst_fn u x e fv_fn e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | not (canBindIn aa nt2 nt2') =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ Just $ printf "forall %s %s %s,\n\
                                      \  %s (%s %s %s %s) [=] %s %s"
                                      e u x
                                      fv_fn subst_fn u x e fv_fn e
             }

      thm _ _ _ _ _ _ | otherwise = return Nothing

{- | @remove x (fv e) [<=] fv (subst e' x e)@. -}

fv_subst_lower :: ASTAnalysis -> [NtRoot] -> M String
fv_subst_lower aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let proof = map head proofs
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      pf _ _ _ _ _ _ =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ mutPfStart Prop types ++
                        defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ subst_fn ++ "_lower"
             }

      thm aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s (%s %s) [<=] %s (%s %s %s %s)"
                        e u x
                        mvSetRemove x fv_fn e fv_fn subst_fn u x e
             }

      thm aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s [<=] %s (%s %s %s %s)"
                        e u x
                        fv_fn e fv_fn subst_fn u x e
             }

{- | @x `notin` fv (subst u y e)@ when
     @x `notin` fv u@ and @x `notin` fv e@. -}

fv_subst_notin :: ASTAnalysis -> [NtRoot] -> M String
fv_subst_notin aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let proof = map head proofs
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      pf _ _ _ _ _ _ =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ mutPfStart Prop types ++
                        defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ subst_fn ++ "_notin"
             }

      fvHyp nt2 nt2' y fv u
          | canBindIn aaa nt2 nt2' = printf "  %s %s %s %s ->\n" y mvSetNotin fv u
          | otherwise              = ""

      thm aa nt1 nt2 mv2 nt2' mv2' =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; y        <- newName mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; fv_fn'   <- fvName aa nt2' mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s)"
                        e u x y
                        y mvSetNotin fv_fn e
                        (fvHyp nt2 nt2' y fv_fn' u)
                        y mvSetNotin fv_fn subst_fn u x e
             }

{- | @fv (subst e' x e) [<=] fv e' `union` remove x (fv e)@. -}

fv_subst_upper :: ASTAnalysis -> [NtRoot] -> M String
fv_subst_upper aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; proofs   <- processNt1Nt2Mv2' aaa nt1s pf
       ; let proof = map head proofs
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      pf _ _ _ _ _ _ =
          do { types    <- processNt1 aaa nt1s ntType
             ; return $ mutPfStart Prop types ++
                        defaultSimp ++ "; " ++ fsetdecTac ++ "."
             }

      name aa nt1 _ mv2 _ mv2' =
          do { fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ fv_fn ++ "_" ++ subst_fn ++ "_upper"
             }

      thm aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; fv_fn2   <- fvName aa nt2' mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [<=] %s %s %s %s %s (%s %s)"
                        e u x
                        fv_fn subst_fn u x e fv_fn2 u mvSetUnion mvSetRemove x fv_fn e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; fv_fn2   <- fvName aa nt2' mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [<=] %s %s %s %s %s"
                        e u x
                        fv_fn subst_fn u x e fv_fn2 u mvSetUnion fv_fn e
             }

      thm aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { e        <- newName nt1
             ; u        <- newName nt2'
             ; x        <- newName mv2'
             ; fv_fn    <- fvName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2'
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (%s %s %s %s) [<=] %s %s"
                        e u x
                        fv_fn subst_fn u x e fv_fn e
             }
