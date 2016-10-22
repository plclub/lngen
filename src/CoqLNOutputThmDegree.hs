{-# LANGUAGE FlexibleContexts #-}

module CoqLNOutputThmDegree where

import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators

degreeThms :: ASTAnalysis -> [[NtRoot]] -> M String
degreeThms aa nts =
    do { degree_Os             <- mapM (local . degree_O aa) nts
       ; degree_Ss             <- mapM (local . degree_S aa) nts
       ; degree_close_recs     <- mapM (local . degree_close_rec aa) nts
       ; degree_closes         <- mapM (local . degree_close aa) nts
       ; degree_close_inv_recs <- mapM (local . degree_close_inv_rec aa) nts
       ; degree_close_invs     <- mapM (local . degree_close_inv aa) nts
       ; degree_open_recs      <- mapM (local . degree_open_rec aa) nts
       ; degree_opens          <- mapM (local . degree_open aa) nts
       ; degree_open_inv_recs  <- mapM (local . degree_open_inv_rec aa) nts
       ; degree_open_invs      <- mapM (local . degree_open_inv aa) nts
       ; return $ printf "Ltac %s ::= auto with %s; tauto.\n\
                         \Ltac %s ::= fail.\n\
                         \\n"
                         defaultAuto hintDb
                         defaultAutoRewr ++
                  concat degree_Ss ++
                  concat degree_Os ++
                  concat degree_close_recs ++
                  concat degree_closes ++
                  concat degree_close_inv_recs ++
                  concat degree_close_invs ++
                  concat degree_open_recs ++
                  concat degree_opens ++
                  concat degree_open_inv_recs ++
                  concat degree_open_invs ++ "\n"
       }

{- | @degree 0 e@ implies @degree k e@. -}

degree_O :: ASTAnalysis -> [NtRoot] -> M String
degree_O aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; return $ degree ++ "_O"
             }

      gen aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; e      <- newName nt1
             ; k      <- newName bvarRoot
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s %s ->\n\
                                 \  %s %s %s"
                                 k e
                                 degree "O" e
                                 degree k e
             ; let proof = printf "induction %s; %s." k defaultSimp
             ; return (stmt, proof)
             }

{- | @degree k e@ implies @degree (S k) e@. -}

degree_S :: ASTAnalysis -> [NtRoot] -> M String
degree_S aaa nt1s =
    do { thms    <- processNt1Nt2Mv2 aaa nt1s thm
       ; names   <- processNt1Nt2Mv2 aaa nt1s name
       ; degrees <- processNt1Nt2Mv2 aaa nt1s (\aa nt1 _ mv2 -> degreeName aa nt1 mv2)
       ; let proof = map (finish . mutPfStart Prop) degrees
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      finish str = str ++ defaultSimp ++ "."

      name aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; return $ degree ++ "_S"
             }

      thm aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; e      <- newName nt1
             ; k      <- newName bvarRoot
             ; return $ printf "forall %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s (S %s) %s"
                               k e
                               degree k e
                               degree k e
             }

{- | @degree (S k) (close_rec k x e)@ when @degree k e@. -}

degree_close_rec :: ASTAnalysis -> [NtRoot] -> M String
degree_close_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2' aaa nt1s thm
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; return $ degree ++ "_" ++ close_fn
             }

      thm aa nt1 _ mv2 _ mv2' | mv2 == mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; k        <- newName bvarRoot
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s (S %s) (%s %s %s %s)"
                               e x k
                               degree k e
                               degree k close_fn k x e
             }

      thm aa nt1 _ mv2 _ mv2' | otherwise =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; k        <- newName bvarRoot
             ; k'       <- newName bvarRoot
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s %s (%s %s %s %s)"
                               e x k k'
                               degree k' e
                               degree k' close_fn k x e
             }

{- | @degree 1 (close x e)@ when @degree 0 e@. -}

degree_close :: ASTAnalysis -> [NtRoot] -> M String
degree_close aaa nt1s =
    do { gens  <- processNt1Nt2Mv2' aaa nt1s gen
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; return $ degree ++ "_" ++ close_fn
             }

      gen aa nt1 _ mv2 _ mv2' | mv2 == mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s 0 %s ->\n\
                                 \  %s 1 (%s %s %s)"
                                 e x
                                 degree e
                                 degree close_fn x e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

      gen aa nt1 _ mv2 _ mv2' | otherwise =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; k        <- newName bvarRoot
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s %s ->\n\
                                 \  %s %s (%s %s %s)"
                                 e x k
                                 degree k e
                                 degree k close_fn x e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @degree n e@ when @degree (S n) (close_rec n x e)@. -}

degree_close_inv_rec :: ASTAnalysis -> [NtRoot] -> M String
degree_close_inv_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2' aaa nt1s thm
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++
                             printf "; eauto with %s." hintDb)
       ; mutualLemmaText2 Immediate NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; return $ degree ++ "_" ++ close_fn ++ "_inv"
             }

      thm aa nt1 _ mv2 _ mv2' | mv2 == mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; k        <- newName bvarRoot
             ; return $ printf "forall %s %s %s,\n\
                               \  %s (S %s) (%s %s %s %s) ->\n\
                               \  %s %s %s"
                               e x k
                               degree k close_fn k x e
                               degree k e
             }

      thm aa nt1 _ mv2 _ mv2' | otherwise =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; k        <- newName bvarRoot
             ; k'       <- newName bvarRoot
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s (%s %s %s %s) ->\n\
                               \  %s %s %s"
                               e x k k'
                               degree k' close_fn k x e
                               degree k' e
             }

{- | @degree 0 e@ when @degree 1 (close x e)@. -}

degree_close_inv :: ASTAnalysis -> [NtRoot] -> M String
degree_close_inv aaa nt1s =
    do { gens  <- processNt1Nt2Mv2' aaa nt1s gen
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Immediate NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; return $ degree ++ "_" ++ close_fn ++ "_inv"
             }

      gen aa nt1 _ mv2 _ mv2' | mv2 == mv2' =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s 1 (%s %s %s) ->\n\
                                 \  %s 0 %s"
                                 e x
                                 degree close_fn x e
                                 degree e
             ; let proof = printf "unfold %s; eauto with %s." close_fn hintDb
             ; return (stmt, proof)
             }

      gen aa nt1 _ mv2 _ mv2' | otherwise =
          do { degree   <- degreeName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; e        <- newName nt1
             ; x        <- newName mv2'
             ; k        <- newName bvarRoot
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s (%s %s %s) ->\n\
                                 \  %s %s %s"
                                 e x k
                                 degree k close_fn x e
                                 degree k e
             ; let proof = printf "unfold %s; eauto with %s." close_fn hintDb
             ; return (stmt, proof)
             }

{- | @degree n (open_rec n u e)@ when
     @degree n u@ and @degree (S n) e@. -}

degree_open_rec :: ASTAnalysis -> [NtRoot] -> M String
degree_open_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2' aaa nt1s thm
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree  <- degreeName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ degree ++ "_" ++ open_fn
             }

      thm aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { k       <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; degree' <- degreeName aa nt2' mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ printf
               "forall %s %s %s,\n\
               \  %s (S %s) %s ->\n\
               \  %s %s %s ->\n\
               \  %s %s (%s %s %s %s)"
               e u k
               degree k e
               degree' k  u
               degree k open_fn k u e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { k       <- newName bvarRoot
             ; k'      <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; degree' <- degreeName aa nt2' mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ printf
               "forall %s %s %s %s,\n\
               \  %s %s %s ->\n\
               \  %s %s %s ->\n\
               \  %s %s (%s %s %s %s)"
               e u k k'
               degree k e
               degree' k  u
               degree k open_fn k' u e
             }

      thm aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { k       <- newName bvarRoot
             ; k'      <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ printf
               "forall %s %s %s %s,\n\
               \  %s %s %s ->\n\
               \  %s %s (%s %s %s %s)"
               e u k k'
               degree k e
               degree k open_fn k' u e
             }

{- | @degree 0 (open e u)@ when
     @degree 0 u@ and @degree 1 e@. -}

degree_open :: ASTAnalysis -> [NtRoot] -> M String
degree_open aaa nt1s =
    do { gens  <- processNt1Nt2Mv2' aaa nt1s gen
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree  <- degreeName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             ; return $ degree ++ "_" ++ open_fn
             }

      gen aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; degree' <- degreeName aa nt2' mv2
             ; open_fn <- openName aa nt1 mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s 1 %s ->\n\
                                 \  %s 0 %s ->\n\
                                 \  %s 0 (%s %s %s)"
                                 e u
                                 degree e
                                 degree' u
                                 degree open_fn e u
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

      gen aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; k       <- newName bvarRoot
             ; degree  <- degreeName aa nt1 mv2
             ; degree' <- degreeName aa nt2' mv2
             ; open_fn <- openName aa nt1 mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s %s ->\n\
                                 \  %s %s %s ->\n\
                                 \  %s %s (%s %s %s)"
                                 e u k
                                 degree k e
                                 degree' k u
                                 degree k open_fn e u
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

      gen aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; k       <- newName bvarRoot
             ; degree  <- degreeName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s %s ->\n\
                                 \  %s %s (%s %s %s)"
                                 e u k
                                 degree k e
                                 degree k open_fn e u
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @degree (S n) e@ when @degree n (open_rec n u e)@. -}

degree_open_inv_rec :: ASTAnalysis -> [NtRoot] -> M String
degree_open_inv_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2' aaa nt1s thm
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++
                             printf "; eauto with %s." hintDb)
       ; mutualLemmaText2 Immediate NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree  <- degreeName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ degree ++ "_" ++ open_fn ++ "_inv"
             }

      thm aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { k       <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ printf
               "forall %s %s %s,\n\
               \  %s %s (%s %s %s %s) ->\n\
               \  %s (S %s) %s"
               e u k
               degree k open_fn k u e
               degree k e
             }

      thm aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { k       <- newName bvarRoot
             ; k'      <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; open_fn <- openRecName aa nt1 mv2'
             ; return $ printf
               "forall %s %s %s %s,\n\
               \  %s %s (%s %s %s %s) ->\n\
               \  %s %s %s"
               e u k k'
               degree k open_fn k' u e
               degree k e
             }

{- | @degree 1 e@ when @degree 0 (open e u)@. -}

degree_open_inv :: ASTAnalysis -> [NtRoot] -> M String
degree_open_inv aaa nt1s =
    do { gens  <- processNt1Nt2Mv2' aaa nt1s gen
       ; names <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Immediate NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { degree  <- degreeName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             ; return $ degree ++ "_" ++ open_fn ++ "_inv"
             }

      gen aa nt1 _ mv2 nt2' mv2' | mv2 == mv2' =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; degree  <- degreeName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s 0 (%s %s %s) ->\n\
                                 \  %s 1 %s"
                                 e u
                                 degree open_fn e u
                                 degree e
             ; let proof = printf "unfold %s; eauto with %s." open_fn hintDb
             ; return (stmt, proof)
             }

      gen aa nt1 _ mv2 nt2' mv2' | otherwise =
          do { e       <- newName nt1
             ; u       <- newName nt2'
             ; k       <- newName bvarRoot
             ; degree  <- degreeName aa nt1 mv2
             ; open_fn <- openName aa nt1 mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s (%s %s %s) ->\n\
                                 \  %s %s %s"
                                 e u k
                                 degree k open_fn e u
                                 degree k e
             ; let proof = printf "unfold %s; eauto with %s." open_fn hintDb
             ; return (stmt, proof)
             }
