{-# LANGUAGE FlexibleContexts #-}
module CoqLNOutputThmSize where

import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators

sizeThms :: ASTAnalysis -> [[NtRoot]] -> M String
sizeThms aa nts =
    do { size_close_recs    <- mapM (local . size_close_rec aa) nts
       ; size_closes        <- mapM (local . size_close aa) nts
       ; size_mins          <- mapM (local . size_min aa) nts
       ; size_open_recs     <- mapM (local . size_open_rec aa) nts
       ; size_opens         <- mapM (local . size_open aa) nts
       ; size_open_var_recs <- mapM (local . size_open_var_rec aa) nts
       ; size_open_vars     <- mapM (local . size_open_var aa) nts
       ; return $ printf "Ltac %s ::= auto with arith %s; tauto.\n\
                         \Ltac %s ::= fail.\n\
                         \\n"
                         defaultAuto hintDb
                         defaultAutoRewr ++
                  concat size_mins ++
                  concat size_close_recs ++
                  concat size_closes ++
                  concat size_open_recs ++
                  concat size_opens ++
                  concat size_open_var_recs ++
                  concat size_open_vars ++ "\n"
       }

{- | @size (close_rec n x e) = size e@. -}

size_close_rec :: ASTAnalysis -> [NtRoot] -> M String
size_close_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeRecName aa nt1 mv2
             ; size_fn  <- sizeName aa nt1
             ; return $ size_fn ++ "_" ++ close_fn
             }

      thm aa nt1 _ mv2 =
          do { k        <- newName bvarRoot
             ; x        <- newName mv2
             ; e        <- newName nt1
             ; close_fn <- closeRecName aa nt1 mv2
             ; size_fn  <- sizeName aa nt1
             ; return $ printf
               "forall %s %s %s,\n\
               \  %s (%s %s %s %s) = %s %s"
               e x k size_fn close_fn k x e size_fn e
             }

{- | @size (close e x) = size e@. -}

size_close :: ASTAnalysis -> [NtRoot] -> M String
size_close aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { close_fn <- closeName aa nt1 mv2
             ; size_fn  <- sizeName aa nt1
             ; return $ size_fn ++ "_" ++ close_fn
             }

      gen aa nt1 _ mv2 =
          do { x        <- newName mv2
             ; e        <- newName nt1
             ; close_fn <- closeName aa nt1 mv2
             ; size_fn  <- sizeName aa nt1
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s (%s %s %s) = %s %s"
                                 e x size_fn close_fn x e size_fn e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @1 <= size e@. -}

size_min :: ASTAnalysis -> [NtRoot] -> M String
size_min aaa nt1s =
    do { thms  <- processNt1 aaa nt1s thm
       ; names <- processNt1 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = mutPfStart Prop types ++ defaultSimp ++ "."
       ; mutualLemmaText Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 =
          do { fn <- sizeName aa nt1
             ; return $ fn ++ "_min"
             }

      thm aa nt1 =
          do { e <- newName nt1
             ; n <- sizeName aa nt1
             ; return $ printf "forall %s, 1 <= %s %s" e n e
             }

{- | @size e <= size (open_rec n e' e)@. -}

size_open_rec :: ASTAnalysis -> [NtRoot] -> M String
size_open_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openRecName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; return $ size_fn ++ "_" ++ open_fn
             }

      thm aa nt1 nt2 mv2 =
          do { k       <- newName bvarRoot
             ; e       <- newName nt1
             ; u       <- newName nt2
             ; open_fn <- openRecName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s <= %s (%s %s %s %s)"
                        e u k
                        size_fn e size_fn open_fn k u e
             }

{- | @size e <= size (open e e')@. -}

size_open :: ASTAnalysis -> [NtRoot] -> M String
size_open aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; return $ size_fn ++ "_" ++ open_fn
             }

      gen aa nt1 nt2 mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; e       <- newName nt1;
             ; u       <- newName nt2;
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s <= %s (%s %s %s)"
                                 e u
                                 size_fn e size_fn open_fn e u
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @size (open_rec n (var x) e) = size e@. -}

size_open_var_rec :: ASTAnalysis -> [NtRoot] -> M String
size_open_var_rec aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openRecName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; return $ size_fn ++ "_" ++ open_fn ++ "_var"
             }

      thm aa nt1 nt2 mv2 =
          do { open_fn <- openRecName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; constr  <- getFreeVarConstr aa nt2 mv2
             ; e       <- newName nt1
             ; x       <- newName mv2
             ; k       <- newName bvarRoot
             ; return $ printf
               "forall %s %s %s,\n\
               \  %s (%s %s (%s %s) %s) = %s %s"
               e x k
               size_fn open_fn k (toName constr) x e size_fn e
             }

{- | @size (open e (var x)) = size e@. -}

size_open_var :: ASTAnalysis -> [NtRoot] -> M String
size_open_var aaa nt1s =
    do { gens     <- processNt1Nt2Mv2 aaa nt1s gen
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve Rewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; return $ size_fn ++ "_" ++ open_fn ++ "_var"
             }

      gen aa nt1 nt2 mv2 =
          do { open_fn <- openName aa nt1 mv2
             ; size_fn <- sizeName aa nt1
             ; constr  <- getFreeVarConstr aa nt2 mv2
             ; e       <- newName nt1
             ; x       <- newName mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s (%s %s (%s %s)) = %s %s"
                                 e x
                                 size_fn open_fn e (toName constr) x size_fn e
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }
