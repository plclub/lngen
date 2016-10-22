{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fcontext-stack=50 #-}

module CoqLNOutputThmOpenClose where

import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators

openCloseThms :: ASTAnalysis -> [[NtRoot]] -> M String
openCloseThms aa nts =
    do { close_inj_recs  <- mapM (local . close_inj_rec aa) nts
       ; close_injs      <- mapM (local . close_inj aa) nts
       ; close_open_recs <- mapM (local . close_open_rec aa) nts
       ; close_opens     <- mapM (local . close_open aa) nts
       ; open_close_recs <- mapM (local . open_close_rec aa) nts
       ; open_closes     <- mapM (local . open_close aa) nts
       ; open_inj_recs   <- mapM (local . open_inj_rec aa) nts
       ; open_injs       <- mapM (local . open_inj aa) nts
       ; return $ printf "Ltac %s ::= auto with %s %s; tauto.\n\
                         \Ltac %s ::= fail.\n\
                         \\n"
                         defaultAuto hintDb bruteDb
                         defaultAutoRewr ++
                  concat close_inj_recs ++
                  concat close_injs ++
                  concat close_open_recs ++
                  concat close_opens ++
                  concat open_close_recs ++
                  concat open_closes ++
                  concat open_inj_recs ++
                  concat open_injs ++ "\n"
       }

{- | @close_rec k x e1 = close_rec k x e2@ implies @e1 = e2@. -}

close_inj_rec :: ASTAnalysis -> [NtRoot] -> M String
close_inj_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = mutPfStart Prop types ++
                     "intros; match goal with\n\
                     \          | |- _ = ?term => destruct term\n\
                     \        end;\n" ++
                     defaultSimp ++ printf "; eauto with %s." hintDb
       ; mutualLemmaText2 Immediate NoRewrite Hide [hintDb] Prop names thms (repeat proof)
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; return $ close_fn ++ "_inj"
             }

      thm aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; e1       <- newName nt1
             ; e2       <- newName nt1
             ; x        <- newName mv2
             ; k        <- newName bvarRoot
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s %s = %s %s %s %s ->\n\
                               \  %s = %s"
                               e1 e2 x k
                               close_fn k x e1 close_fn k x e2
                               e1 e2
             }

{- | @close x e1 = close x e2@ implies @e1 = e2@. -}

close_inj :: ASTAnalysis -> [NtRoot] -> M String
close_inj aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Immediate NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; return $ close_fn ++ "_inj"
             }

      gen aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; e1       <- newName nt1
             ; e2       <- newName nt1
             ; x        <- newName mv2
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s %s = %s %s %s ->\n\
                                 \  %s = %s"
                                 e1 e2 x
                                 close_fn x e1 close_fn x e2
                                 e1 e2
             ; let proof = printf "unfold %s; eauto with %s." close_fn hintDb
             ; return (stmt, proof)
             }

{- | @close_rec k x (open_rec k x e) = e@ when @x `notin` fv e@. -}

close_open_rec :: ASTAnalysis -> [NtRoot] -> M String
close_open_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2
             ; return $ close_fn ++ "_" ++ open_fn
             }

      thm aa nt1 nt2 mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; e        <- newName nt1
             ; x        <- newName mv2
             ; k        <- newName bvarRoot
             ; constr   <- getFreeVarConstr aa nt2 mv2
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s (%s %s (%s %s) %s) = %s"
                               e x k
                               x mvSetNotin fv_fn e
                               close_fn k x open_fn k (toName constr) x e e
             }

{- | @close x (open x e) = e@ when @x `notin` fv e@. -}

close_open :: ASTAnalysis -> [NtRoot] -> M String
close_open aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2
             ; return $ close_fn ++ "_" ++ open_fn
             }

      gen aa nt1 nt2 mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; e        <- newName nt1
             ; x        <- newName mv2
             ; constr   <- getFreeVarConstr aa nt2 mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s %s %s ->\n\
                                 \  %s %s (%s %s (%s %s)) = %s"
                                 e x
                                 x mvSetNotin fv_fn e
                                 close_fn x open_fn e (toName constr) x e
             ; let proof = printf "unfold %s; unfold %s; %s." close_fn open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @open_rec k x (close_rec k x e) = e@ -}

open_close_rec :: ASTAnalysis -> [NtRoot] -> M String
open_close_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2
             ; return $ open_fn ++ "_" ++ close_fn
             }

      thm aa nt1 nt2 mv2 =
          do { k        <- newName bvarRoot
             ; x        <- newName mv2
             ; e        <- newName nt1
             ; close_fn <- closeRecName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2
             ; constr   <- getFreeVarConstr aa nt2 mv2
             ; return $ printf
               "forall %s %s %s,\n\
               \  %s %s (%s %s) (%s %s %s %s) = %s"
               e x k
               open_fn k (toName constr) x close_fn k x e e
             }

{- | @open x (close x e) = e@ -}

open_close :: ASTAnalysis -> [NtRoot] -> M String
open_close aaa nt1s =
    do { gens     <- processNt1Nt2Mv2 aaa nt1s gen
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2
             ; return $ open_fn ++ "_" ++ close_fn
             }

      gen aa nt1 nt2 mv2 =
          do { x        <- newName mv2
             ; e        <- newName nt1
             ; close_fn <- closeName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2
             ; constr   <- getFreeVarConstr aa nt2 mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s (%s %s %s) (%s %s) = %s"
                                 e x
                                 open_fn close_fn x e (toName constr) x e
             ; let proof = printf "unfold %s; unfold %s; %s."
                                  close_fn open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @open_rec k x e1 = open_rec k x e2@ implies @e1 = e2@ when
     @x `notin` fv e1 `union` fv e2@. -}

open_inj_rec :: ASTAnalysis -> [NtRoot] -> M String
open_inj_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = mutPfStart Prop types ++
                     "intros; match goal with\n\
                     \          | |- _ = ?term => destruct term\n\
                     \        end;\n" ++
                     printf "%s; eauto with %s." defaultSimp hintDb
       ; mutualLemmaText2 Immediate NoRewrite Hide [hintDb] Prop names thms (repeat proof)
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openRecName aa nt1 mv2
             ; return $ open_fn ++ "_inj"
             }

      thm aa nt1 nt2 mv2 =
          do { e2      <- newName nt1
             ; e1      <- newName nt1
             ; k       <- newName bvarRoot
             ; x       <- newName mv2
             ; open_fn <- openRecName aa nt1 mv2
             ; fv_fn   <- fvName aa nt1 mv2
             ; constr  <- getFreeVarConstr aa nt2 mv2
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s (%s %s) %s = %s %s (%s %s) %s ->\n\
                               \  %s = %s"
                               e1 e2 x k
                               x mvSetNotin fv_fn e1
                               x mvSetNotin fv_fn e2
                               open_fn k (toName constr) x e1 open_fn k (toName constr) x e2
                               e1 e2
             }

{- | @open e1 x = open e2 x@ implies @e1 = e2@ when
     @x `notin` fv e1 `union` fv e2@. -}

open_inj :: ASTAnalysis -> [NtRoot] -> M String
open_inj aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Immediate NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; return $ open_fn ++ "_inj"
             }

      gen aa nt1 nt2 mv2 =
          do { e2       <- newName nt1
             ; e1       <- newName nt1
             ; x        <- newName mv2
             ; open_fn  <- openName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; constr   <- getFreeVarConstr aa nt2 mv2
             -- ORDER TO OPEN
             ; let stmt = printf"forall %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s (%s %s) = %s %s (%s %s) ->\n\
                               \  %s = %s"
                               e1 e2 x
                               x mvSetNotin fv_fn e1
                               x mvSetNotin fv_fn e2
                               open_fn e1 (toName constr) x open_fn e2 (toName constr) x
                               e1 e2
             ; let proof = printf "unfold %s; eauto with %s." open_fn hintDb
             ; return (stmt, proof)
             }

