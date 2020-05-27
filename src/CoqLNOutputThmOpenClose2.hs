{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -freduction-depth=50 #-}

module CoqLNOutputThmOpenClose2 where

import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators

openCloseThms2 :: ASTAnalysis -> [[NtRoot]] -> M String
openCloseThms2 aa nts =
    do { close_degree_recs <- mapM (local . close_degree_rec aa) nts
       ; close_lcs         <- mapM (local . close_lc aa) nts
       ; open_degree_recs  <- mapM (local . open_degree_rec aa) nts
       ; open_lcs          <- mapM (local . open_lc aa) nts
       ; return $ printf "Ltac %s ::= auto with %s; tauto.\n\
                         \Ltac %s ::= fail.\n\
                         \\n"
                         defaultAuto hintDb
                         defaultAutoRewr ++
                  concat close_degree_recs ++
                  concat close_lcs ++
                  concat open_degree_recs ++
                  concat open_lcs ++ "\n"
       }

{- | @close_rec k x e = e@ when @degree k e@ and @x `notin` fv e@. -}

close_degree_rec :: ASTAnalysis -> [NtRoot] -> M String
close_degree_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; degree   <- degreeName aa nt1 mv2
             ; return $ close_fn ++ "_" ++ degree
             }

      thm aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; degree   <- degreeName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; e        <- newName nt1
             ; x        <- newName mv2
             ; k        <- newName bvarRoot
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s %s = %s"
                               e x k
                               degree k e
                               x mvSetNotin fv_fn e
                               close_fn k x e e
             }

{- | @close x e = e@ when @lc e@ and @x `notin` fv e@. -}

close_lc :: ASTAnalysis -> [NtRoot] -> M String
close_lc aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; lc       <- lcName aa nt1
             ; return $ close_fn ++ "_" ++ lc
             }

      gen aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; lc       <- lcName aa nt1
             ; fv_fn    <- fvName aa nt1 mv2
             ; e        <- newName nt1
             ; x        <- newName mv2
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s ->\n\
                                 \  %s %s %s %s ->\n\
                                 \  %s %s %s = %s"
                                 e x
                                 lc e
                                 x mvSetNotin fv_fn e
                                 close_fn x e e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @open_rec n u e = e@ when @degree n e@. -}

open_degree_rec :: ASTAnalysis -> [NtRoot] -> M String
open_degree_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openRecName aa nt1 mv2
             ; degree  <- degreeName aa nt1 mv2
             ; return $ open_fn ++ "_" ++ degree
             }

      thm aa nt1 nt2 mv2 =
          do { open_fn <- openRecName aa nt1 mv2
             ; degree  <- degreeName aa nt1 mv2
             ; n <- newName bvarRoot
             ; u <- newName nt2
             ; e <- newName nt1
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s %s %s %s = %s"
                               e u n
                               degree n e
                               open_fn n u e e
             }


{- | @open u e = e@ when @lc e@. -}

open_lc :: ASTAnalysis -> [NtRoot] -> M String
open_lc aaa nt1s =
    do { gens     <- processNt1Nt2Mv2 aaa nt1s gen
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; lc      <- lcName aa nt1
             ; return $ open_fn ++ "_" ++ lc
             }

      gen aa nt1 nt2 mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; lc      <- lcName aa nt1
             ; u <- newName nt2
             ; e <- newName nt1
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s ->\n\
                                 \  %s %s %s = %s"
                                 e u
                                 lc e
                                 open_fn e u e
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }
