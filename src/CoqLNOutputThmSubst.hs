{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fcontext-stack=50 #-}

module CoqLNOutputThmSubst where

import Data.Maybe  ( catMaybes )
import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators
import MyLibrary ( sepStrings )

substThms :: ASTAnalysis -> [[NtRoot]] -> M String
substThms aa nts =
    do { subst_close_recs      <- mapM (local . subst_close_rec aa) nts
       ; subst_closes          <- mapM (local . subst_close aa) nts
       ; subst_close_open_recs <- mapM (local . subst_close_open_rec aa) nts
       ; subst_close_opens     <- mapM (local . subst_close_open aa) nts
       ; subst_constrs         <- mapM (local . subst_constr aa) nts
       ; subst_degrees         <- mapM (local . subst_degree aa) nts
       ; subst_fresh_eqs       <- mapM (local . subst_fresh_eq aa) nts
       ; subst_fresh_sames     <- mapM (local . subst_fresh_same aa) nts
       ; subst_freshs          <- mapM (local . subst_fresh aa) nts
       ; subst_intro_recs      <- mapM (local . subst_intro_rec aa) nts
       ; subst_intros          <- mapM (local . subst_intro aa) nts
       ; subst_lcs             <- mapM (local . subst_lc aa) nts
       ; subst_open_recs       <- mapM (local . subst_open_rec aa) nts
       ; subst_opens           <- mapM (local . subst_open aa) nts
       ; subst_open_vars       <- mapM (local . subst_open_var aa) nts
       ; subst_spec_recs       <- mapM (local . subst_spec_rec aa) nts
       ; subst_specs           <- mapM (local . subst_spec aa) nts
       ; subst_substs          <- mapM (local . subst_subst aa) nts
       ; return $ printf "Ltac %s ::= auto with %s %s; tauto.\n\
                         \Ltac %s ::= autorewrite with %s.\n\
                         \\n"
                         defaultAuto hintDb bruteDb
                         defaultAutoRewr hintDb++
                  concat subst_close_recs ++
                  concat subst_closes ++
                  concat subst_degrees ++
                  concat subst_fresh_eqs ++
                  concat subst_fresh_sames ++
                  concat subst_freshs ++
                  concat subst_lcs ++
                  concat subst_open_recs ++
                  concat subst_opens ++
                  concat subst_open_vars ++
                  concat subst_spec_recs ++
                  concat subst_specs ++
                  concat subst_substs ++
                  concat subst_close_open_recs ++
                  concat subst_close_opens ++
                  (concat $ concat subst_constrs) ++
                  concat subst_intro_recs ++
                  concat subst_intros ++ "\n"
       }

{- | @subxt u x (close_rec k y e) = close_rec k y (subst u x e)@
     when @x <> y@ and @y `notin` fv u@ and @degree k u@. -}

subst_close_rec :: ASTAnalysis -> [NtRoot] -> M String
subst_close_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; return $ subst_fn ++ "_" ++ close_fn
             }

      neq mv2 mv2' x y | mv2 == mv2' = printf "  %s <> %s ->\n" x y
                       | otherwise   = ""

      fv nt2 nt2' y fv_fn u
          | canBindIn aaa nt2' nt2 = printf "  %s %s %s %s ->\n" y mvSetNotin fv_fn u
          | otherwise              = ""

      deg nt2 nt2' d k u
          | canBindIn aaa nt2' nt2 = printf "  %s %s %s ->\n" d k u
          | otherwise              = ""

      thm aa nt1 nt2 mv2 nt2' mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; fv_fn    <- fvName aa nt2 mv2'
             ; degree   <- degreeName aa nt2 mv2'
             ; x        <- newName mv2'
             ; y        <- newName mv2
             ; k        <- newName bvarRoot
             ; u        <- newName nt2
             ; e        <- newName nt1
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \%s\
                               \%s\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s %s %s (%s %s %s %s)"
                               e u x y k
                               (deg nt2 nt2' degree k u)
                               (neq mv2 mv2' x y)
                               (fv nt2 nt2' y fv_fn u)
                               subst_fn u x close_fn k y e
                               close_fn k y subst_fn u x e
             }

{- | @subxt u x (close y e) = close y (subst u x e)@
     when @x <> y@ and @y `notin` fv u@ and @lc u@. -}

subst_close :: ASTAnalysis -> [NtRoot] -> M String
subst_close aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; return $ subst_fn ++ "_" ++ close_fn
             }

      neq mv2 mv2' x y | mv2 == mv2' = printf "  %s <> %s ->\n" x y
                       | otherwise   = ""

      fv nt2 nt2' y fv_fn u
          | canBindIn aaa nt2' nt2 = printf "  %s %s %s %s ->\n" y mvSetNotin fv_fn u
          | otherwise              = ""

      gen aa nt1 nt2 mv2 nt2' mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; fv_fn    <- fvName aa nt2 mv2'
             ; lc       <- lcName aa nt2
             ; x        <- newName mv2'
             ; y        <- newName mv2
             ; u        <- newName nt2
             ; e        <- newName nt1
             ; let stmt = printf "forall %s %s %s %s,\n\
                                 \  %s %s ->\
                                 \%s\
                                 \%s\
                                 \  %s %s %s (%s %s %s) = %s %s (%s %s %s %s)"
                                 e u x y
                                 lc u
                                 (neq mv2 mv2' x y)
                                 (fv nt2 nt2' y fv_fn u)
                                 subst_fn u x close_fn y e
                                 close_fn y subst_fn u x e
             ; let proof = printf "unfold %s; %s." close_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @subst u x e@ = @close_rec k z (subst u x (open_rec k (var z) e))@
     when @z `notin` fv u `union` fv e `union` { x }@ and @degree k u@. -}

subst_close_open_rec :: ASTAnalysis -> [NtRoot] -> M String
subst_close_open_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Set types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Set names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; open_fn  <- openRecName aa nt1 mv2'
             ; return $ sepStrings "_" [subst_fn, close_fn, open_fn]
             }

      neq mv2 mv2' z x | mv2 == mv2' = printf "  %s <> %s ->\n" z x
                       | otherwise   = ""

      fv nt nt' z fv_fn t
          | canBindIn aaa nt' nt = printf "  %s %s %s %s ->\n" z mvSetNotin fv_fn t
          | otherwise            = ""

      deg nt nt' d k t
          | canBindIn aaa nt' nt = printf "  %s %s %s ->\n" d k t
          | otherwise            = ""

      thm aa nt1 nt2 mv2 nt2' mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeRecName aa nt1 mv2'
             ; open_fn  <- openRecName aa nt1 mv2'
             ; degree   <- degreeName aa nt2 mv2'
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; z        <- newName mv2'
             ; e        <- newName nt1
             ; k        <- newName bvarRoot
             ; fv_fn    <- fvName aa nt1 mv2'
             ; fv_fn'   <- fvName aa nt2 mv2'
             ; constr   <- getFreeVarConstr aa nt2' mv2'
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \%s\
                               \%s\
                               \%s\
                               \%s\
                               \  %s %s %s %s = %s %s %s (%s %s %s (%s %s (%s %s) %s))"
                               e u x z k
                               (fv nt1 nt2' z fv_fn e)
                               (fv nt2 nt2' z fv_fn' u)
                               (neq mv2 mv2' z x)
                               (deg nt2 nt2' degree k u)
                               subst_fn u x e
                               close_fn k z subst_fn u x open_fn k (toName constr) z e
             }

{- | @subst u x e@ = @close_rec k z (subst u x (open_rec k (var z) e))@
     when @z `notin` fv u `union` fv e `union` { x }@ and @lc u@. -}

subst_close_open :: ASTAnalysis -> [NtRoot] -> M String
subst_close_open aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; open_fn  <- openName aa nt1 mv2'
             ; return $ sepStrings "_" [subst_fn, close_fn, open_fn]
             }

      neq mv2 mv2' z x | mv2 == mv2' = printf "  %s <> %s ->\n" z x
                       | otherwise   = ""

      fv nt nt' z fv_fn t
          | canBindIn aaa nt' nt = printf "  %s %s %s %s ->\n" z mvSetNotin fv_fn t
          | otherwise            = ""

      lcHyp nt lc t | isOpenable aaa nt = printf "  %s %s ->\n" lc t
                    | otherwise         = ""

      gen aa nt1 nt2 mv2 nt2' mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; close_fn <- closeName aa nt1 mv2'
             ; open_fn  <- openName aa nt1 mv2'
             ; lc       <- lcName aa nt2
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; z        <- newName mv2'
             ; e        <- newName nt1
             ; fv_fn    <- fvName aa nt1 mv2'
             ; fv_fn'   <- fvName aa nt2 mv2'
             ; constr   <- getFreeVarConstr aa nt2' mv2'
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s %s,\n\
                                 \%s\
                                 \%s\
                                 \%s\
                                 \%s\
                                 \  %s %s %s %s = %s %s (%s %s %s (%s %s (%s %s)))"
                                 e u x z
                                 (fv nt1 nt2' z fv_fn e)
                                 (fv nt2 nt2' z fv_fn' u)
                                 (neq mv2 mv2' z x)
                                 (lcHyp nt2 lc u)
                                 subst_fn u x e
                                 close_fn z subst_fn u x open_fn e (toName constr) z
             ; let proof = printf "unfold %s; unfold %s; %s." close_fn open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | How @subst@ commutes with binding constructors. -}

subst_constr :: ASTAnalysis -> [NtRoot] -> M [String]
subst_constr aaa nt1s =
    sequence $ do { nt1             <- nt1s
                  ; nt2             <- filter (canBindOver aaa nt1) (ntRoots aaa)
                  ; mv2             <- mvsOfNt aaa nt2
                  ; (Syntax _ _ cs) <- [runM [] $ getSyntax aaa nt1]
                  ; c               <- [c | c <- cs, hasBindingArg c]
                  ; return $ local $ thm aaa nt1 nt2 mv2 c
                  }
    where
      thm aa nt1 nt2 mv2 c@(SConstr pos _ _ args _) =
          do { subst_fn <- substName aa nt1 mv2
             ; lc       <- lcName aa nt2
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; glomps   <- mapM (glomp aa pos nt2 mv2 u x) args
             ; let (mvs, nts, args', freshes) = unzip4 glomps
             ; let stmt  = printf "forall %s %s %s %s,\n\
                                  \%s\
                                  \%s\
                                  \  %s %s %s (%s %s) = %s %s"
                                  (sepStrings " " $ catMaybes mvs) (sepStrings " " nts) u x
                                  (lcHyp nt2 lc u)
                                  (concat $ catMaybes freshes)
                                  subst_fn u x (toName c) (sepStrings " " nts)
                                  (toName c) (sepStrings " " $ map wrap args')
             ; let proof = defaultSimp ++ "."
             ; let name  = subst_fn ++ "_" ++ (toName c)
             ; lemmaText Resolve NoRewrite NoHide [hintDb] name stmt proof
             }

      unzip4 []             = ([], [], [], [])
      unzip4 ((a,b,c,d):xs) = (a:as,b:bs,c:cs,d:ds)
          where
            (as,bs,cs,ds) = unzip4 xs

      wrap s = "(" ++ s ++ ")"

      lcHyp nt2 lc u | isOpenable aaa nt2 = printf "  %s %s ->\n" lc u
                     | otherwise          = ""

      glomp _ pos _ _ _ _ IndexArg = error $ show pos ++ ": Internal error (subst_constr / IndexArg)."

      glomp _ _ _ _ _ _ (MvArg nt) =
          do { n <- newName nt
             ; return $ (Nothing, n, n, Nothing)
             }

      glomp aa _ nt2 mv2 u x (NtArg nt)
          | canBindIn aa nt2 nt =
              do { n  <- newName nt
                 ; subst_fn <- substName aa nt mv2
                 ; return $ (Nothing, n, printf "%s %s %s %s" subst_fn u x n, Nothing)
                 }
          | otherwise =
              do { n <- newName nt
                 ; return $ (Nothing, n, n, Nothing)
                 }

      glomp aa _ nt2 mv2 u x (BindingArg mv' nt' nt)
          | canBindIn aa nt2 nt =
              do { n <- newName nt
                 ; z <- newName mv'
                 ; close_fn <- closeName aa nt mv'
                 ; open_fn  <- openName aa nt mv'
                 ; subst_fn <- substName aa nt mv2
                 ; constr   <- getFreeVarConstr aa nt' mv'
                 ; fv_fnu   <- fvName aa nt2 mv'
                 ; fv_fnn   <- fvName aa nt mv'
                 ; let fvu = if canBindIn aa nt' nt2
                             then Just (printf "%s %s" fv_fnu u)
                             else Nothing
                 ; let fvn = if canBindIn aa nt' nt
                             then Just (printf "%s %s" fv_fnn n)
                             else Nothing
                 ; let fvz = if canonRoot aa mv' == canonRoot aa mv2
                             then Just (printf "%s %s" mvSetSingleton x)
                             else Nothing
                 ; let fresh = catMaybes [fvu, fvn, fvz]
                 ; let hyp = if null fresh
                             then ""
                             else printf "  %s %s %s ->\n" z mvSetNotin (sepStrings (" " ++ mvSetUnion ++ " ") fresh)
                 -- ORDER TO OPEN
                 ; return $ (Just z, n, printf "%s %s (%s %s %s (%s %s (%s %s)))"
                                               close_fn z
                                               subst_fn u x
                                               open_fn n (toName constr) z,
                                        Just hyp)
                 }
          | otherwise =
              do { n <- newName nt
                 ; return $ (Nothing, n, n, Nothing)
                 }

{- | @degree n (subst u x e)@ when @degree n u@ and @degree n e@. -}

subst_degree :: ASTAnalysis -> [NtRoot] -> M String
subst_degree aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; degree   <- degreeName aa nt1 mv2'
             ; return $ subst_fn ++ "_" ++ degree
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2' nt2 =
          do { k         <- newName bvarRoot
             ; e1        <- newName nt1
             ; e2        <- newName nt2
             ; x         <- newName mv2
             ; subst_fn  <- substName aa nt1 mv2
             ; degree    <- degreeName aa nt1 mv2'
             ; degree'   <- degreeName aa nt2 mv2'
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s %s %s ->\n\
                               \  %s %s (%s %s %s %s)"
                               e1 e2 x k
                               degree k e1
                               degree' k e2
                               degree k subst_fn e2 x e1
             }

      thm aa nt1 nt2 mv2 _ mv2' | otherwise =
          do { k         <- newName bvarRoot
             ; e1        <- newName nt1
             ; e2        <- newName nt2
             ; x         <- newName mv2
             ; subst_fn  <- substName aa nt1 mv2
             ; degree    <- degreeName aa nt1 mv2'
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s ->\n\
                               \  %s %s (%s %s %s %s)"
                               e1 e2 x k
                               degree k e1
                               degree k subst_fn e2 x e1
             }

{- | @subst u x e = e@ when @x `notin` fv e@. -}

subst_fresh_eq :: ASTAnalysis -> [NtRoot] -> M String
subst_fresh_eq aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_fresh_eq"
             }

      thm aa nt1 nt2 mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; e        <- newName nt1
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s %s = %s"
                               e u x
                               x mvSetNotin fv_fn e
                               subst_fn u x e e
             }

{- | @x `notin` subst u x e@ when @x `notin` fv u@. -}

subst_fresh_same :: ASTAnalysis -> [NtRoot] -> M String
subst_fresh_same aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_fresh_same"
             }

      thm aa nt1 nt2 mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; fv_fn'   <- fvName aa nt2 mv2
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; e        <- newName nt1
             ; return $ printf "forall %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s (%s %s %s %s)"
                               e u x
                               x mvSetNotin fv_fn' u
                               x mvSetNotin fv_fn subst_fn u x e
             }

{- | @x `notin` subst u y e@ when @x `notin` fv u `union` fv e@. -}

subst_fresh :: ASTAnalysis -> [NtRoot] -> M String
subst_fresh aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_fresh"
             }

      thm aa nt1 nt2 mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; fv_fn'   <- fvName aa nt2 mv2
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; y        <- newName mv2
             ; e        <- newName nt1
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s (%s %s %s %s)"
                               e u x y
                               x mvSetNotin fv_fn e
                               x mvSetNotin fv_fn' u
                               x mvSetNotin fv_fn subst_fn u y e
             }

{- | @open_rec k u e = subst u x (open_rec k x e)@ when @x `notin` fv e@. -}

subst_intro_rec :: ASTAnalysis -> [NtRoot] -> M String
subst_intro_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve Rewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_intro_rec"
             }

      thm aa nt1 nt2 mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; constr   <- getFreeVarConstr aa nt2 mv2
             ; k        <- newName bvarRoot
             ; e        <- newName nt1
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \  %s %s %s %s = %s %s %s (%s %s (%s %s) %s)"
                               e x u k
                               x mvSetNotin fv_fn e
                               open_fn k u e
                               subst_fn u x open_fn k (toName constr) x e
             }

{- | @open_rec k u e = subst u x (open_rec e x)@ when @x `notin` fv e@. -}

subst_intro :: ASTAnalysis -> [NtRoot] -> M String
subst_intro aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_intro"
             }

      gen aa nt1 nt2 mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2
             ; fv_fn    <- fvName aa nt1 mv2
             ; constr   <- getFreeVarConstr aa nt2 mv2
             ; e        <- newName nt1
             ; u        <- newName nt2
             ; x        <- newName mv2
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s %s %s ->\n\
                                 \  %s %s %s = %s %s %s (%s %s (%s %s))"
                                 x e u
                                 x mvSetNotin fv_fn e
                                 open_fn e u
                                 subst_fn u x open_fn e (toName constr) x
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @lc (subst u x e)@ when @lc u@ and @lc e@. -}

subst_lc :: ASTAnalysis -> [NtRoot] -> M String
subst_lc aaa nt1s =
    do { gens     <- processNt1Nt2Mv2 aaa nt1s gen
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { lc       <- lcName aa nt1
             ; subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_" ++ lc
             }

      gen aa nt1 nt2 mv2 =
          do { e1       <- newName nt1
             ; e2       <- newName nt2
             ; x        <- newName mv2
             ; lc       <- lcName aa nt1
             ; lc'      <- lcName aa nt2
             ; subst_fn <- substName aa nt1 mv2
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s ->\n\
                                 \  %s %s ->\n\
                                 \  %s (%s %s %s %s)"
                                 e1 e2 x
                                 lc e1
                                 lc' e2
                                 lc subst_fn e2 x e1
             ; let proof = printf "%s." defaultSimp
             ; return (stmt, proof)
             }

{- | @subst u x (open_rec n v e) = open_rec n (subst u x v) (subst u x e)@
     when @lc u@. -}

subst_open_rec :: ASTAnalysis -> [NtRoot] -> M String
subst_open_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2'
             ; return $ subst_fn ++ "_" ++ open_fn
             }

      lcHyp nt2 nt2' lc u
          | canBindIn aaa nt2' nt2 = printf "  %s %s ->\n" lc u
          | otherwise              = ""

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { subst_fn  <- substName aa nt1 mv2
             ; open_fn   <- openRecName aa nt1 mv2'
             ; u         <- newName nt2
             ; v         <- newName nt2'
             ; x         <- newName mv2
             ; e         <- newName nt1
             ; k         <- newName bvarRoot
             ; subst_fn' <- substName aa nt2' mv2
             ; lc        <- lcName aa nt2
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s %s (%s %s %s %s) (%s %s %s %s)"
                               e u v x k
                               (lcHyp nt2 nt2' lc u)
                               subst_fn u x open_fn k v e
                               open_fn k subst_fn' u x v subst_fn u x e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | otherwise =
          do { subst_fn  <- substName aa nt1 mv2
             ; open_fn   <- openRecName aa nt1 mv2'
             ; u         <- newName nt2
             ; v         <- newName nt2'
             ; x         <- newName mv2
             ; e         <- newName nt1
             ; k         <- newName bvarRoot
             ; lc        <- lcName aa nt2
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s %s %s (%s %s %s %s)"
                               e u v x k
                               (lcHyp nt2 nt2' lc u)
                               subst_fn u x open_fn k v e
                               open_fn k v subst_fn u x e
             }

{- | @subst u x (open e v) = open (subst u x e) (subst u x v)@
     when @lc u@. -}

subst_open :: ASTAnalysis -> [NtRoot] -> M String
subst_open aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2'
             ; return $ subst_fn ++ "_" ++ open_fn
             }

      lcHyp nt2 nt2' lc u
          | canBindIn aaa nt2' nt2 = printf "  %s %s ->\n" lc u
          | otherwise              = ""

      gen aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { subst_fn  <- substName aa nt1 mv2
             ; open_fn   <- openName aa nt1 mv2'
             ; u         <- newName nt2
             ; v         <- newName nt2'
             ; x         <- newName mv2
             ; e         <- newName nt1
             ; subst_fn' <- substName aa nt2' mv2
             ; lc        <- lcName aa nt2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s %s,\n\
                                 \%s\
                                 \  %s %s %s (%s %s %s) = %s (%s %s %s %s) (%s %s %s %s)"
                                 e u v x
                                 (lcHyp nt2 nt2' lc u)
                                 subst_fn u x open_fn e v
                                 open_fn subst_fn u x e subst_fn' u x v
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

      gen aa nt1 nt2 mv2 nt2' mv2' | otherwise =
          do { subst_fn  <- substName aa nt1 mv2
             ; open_fn   <- openName aa nt1 mv2'
             ; u         <- newName nt2
             ; v         <- newName nt2'
             ; x         <- newName mv2
             ; e         <- newName nt1
             ; lc        <- lcName aa nt2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s %s,\n\
                                 \%s\
                                 \  %s %s %s (%s %s %s) = %s (%s %s %s %s) %s"
                                 e u v x
                                 (lcHyp nt2 nt2' lc u)
                                 subst_fn u x open_fn e v
                                 open_fn subst_fn u x e v
             ; let proof = printf "unfold %s; %s." open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @subst u x (open e (var y)) = open (subst u x e) (var y)@
      when @lc u@ and @x <> y@. -}

subst_open_var :: ASTAnalysis -> [NtRoot] -> M String
subst_open_var aaa nt1s =
    do { gens     <- processNt1Nt2Mv2' aaa nt1s gen
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_fn <- substName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2'
             ; return $ subst_fn ++ "_" ++ open_fn ++ "_var"
             }

      lcHyp nt2 nt2' lc u
          | canBindIn aaa nt2' nt2 = printf "  %s %s ->\n" lc u
          | otherwise              = ""

      neq mv2 mv2' x y | mv2 == mv2' = printf "  %s <> %s ->\n" x y
                       | otherwise   = ""

      gen aa nt1 nt2 mv2 nt2' mv2' =
          do { subst_fn  <- substName aa nt1 mv2
             ; open_fn   <- openName aa nt1 mv2'
             ; u         <- newName nt2
             ; x         <- newName mv2
             ; y         <- newName mv2'
             ; constr    <- getFreeVarConstr aa nt2' mv2'
             ; e         <- newName nt1
             ; lc        <- lcName aa nt2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s %s,\n\
                                 \%s\
                                 \%s\
                                 \  %s (%s %s %s %s) (%s %s) = %s %s %s (%s %s (%s %s))"
                                 e u x y
                                 (neq mv2 mv2' x y)
                                 (lcHyp nt2 nt2' lc u)
                                 open_fn subst_fn u x e (toName constr) y
                                 subst_fn u x open_fn e (toName constr) y
             ; let rw = subst_fn ++ "_" ++ open_fn
             ; let proof = printf "intros; rewrite %s; %s." rw defaultSimp
             ; return (stmt, proof)
             }

{- | @subst e2 x e1 = open_rec k e2 (close_rec k x e1)@. -}

subst_spec_rec :: ASTAnalysis -> [NtRoot] -> M String
subst_spec_rec aaa nt1s =
    do { thms     <- processNt1Nt2Mv2 aaa nt1s thm
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite Hide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_spec_rec"
             }

      thm aa nt1 nt2 mv2 =
          do { k        <- newName bvarRoot
             ; e1       <- newName nt1
             ; e2       <- newName nt2
             ; x        <- newName mv2
             ; close_fn <- closeRecName aa nt1 mv2
             ; open_fn  <- openRecName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2
             ; return $ printf "forall %s %s %s %s,\n\
                               \  %s %s %s %s = %s %s %s (%s %s %s %s)"
                        e1 e2 x k
                        subst_fn e2 x e1 open_fn k e2 close_fn k x e1
             }

{- | @subst e2 x e1 = open (close x e1) e2@. -}

subst_spec :: ASTAnalysis -> [NtRoot] -> M String
subst_spec aaa nt1s =
    do { gens     <- processNt1Nt2Mv2 aaa nt1s gen
       ; names    <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { subst_fn <- substName aa nt1 mv2
             ; return $ subst_fn ++ "_spec"
             }

      gen aa nt1 nt2 mv2 =
          do { e1       <- newName nt1
             ; e2       <- newName nt2
             ; x        <- newName mv2
             ; close_fn <- closeName aa nt1 mv2
             ; open_fn  <- openName aa nt1 mv2
             ; subst_fn <- substName aa nt1 mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s %s,\n\
                                 \  %s %s %s %s = %s (%s %s %s) %s"
                                 e1 e2 x
                                 subst_fn e2 x e1 open_fn close_fn x e1 e2
             ; let proof = printf "unfold %s; unfold %s; %s."
                                  close_fn open_fn defaultSimp
             ; return (stmt, proof)
             }

{- | @subst u y (subst u' x e) = subst (subst u y u') x (subst u y e)@
     when @x `notin` fv u@.

     Implementation note (BEA): The case analysis in the function is
     somewhat intense.  Maybe there's a simpler way? -}

subst_subst :: ASTAnalysis -> [NtRoot] -> M String
subst_subst aaa nt1s =
    do { thms     <- processNt1Nt2Mv2' aaa nt1s thm
       ; names    <- processNt1Nt2Mv2' aaa nt1s name
       ; types    <- processNt1 aaa nt1s ntType
       ; let proof = repeat (mutPfStart Prop types ++ defaultSimp ++ ".")
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 _ mv2 _ mv2' =
          do { subst_out <- substName aa nt1 mv2
             ; subst_in  <- substName aa nt1 mv2'
             ; return $ subst_out ++ "_" ++ subst_in
             }

      neq x y mv2 mv2' | mv2 == mv2' = "  " ++ x ++ " <> " ++ y ++ " ->\n"
      neq _ _ _   _    | otherwise   = ""

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' && canBindIn aa nt2' nt2 =
          do { subst_out  <- substName aa nt1 mv2
             ; subst_in   <- substName aa nt1 mv2'
             ; subst_new  <- substName aa nt2' mv2
             ; fv_fn      <- fvName aa nt2 mv2'
             ; e          <- newName nt1
             ; u          <- newName nt2
             ; y          <- newName mv2
             ; u'         <- newName nt2'
             ; x          <- newName mv2'
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s (%s %s %s %s) %s (%s %s %s %s)"
                               e u u' x y
                               x mvSetNotin fv_fn u
                               (neq x y mv2 mv2')
                               subst_out u y subst_in u' x e
                               subst_in subst_new u y u' x subst_out u y e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2 nt2' =
          do { subst_out  <- substName aa nt1 mv2
             ; subst_in   <- substName aa nt1 mv2'
             ; subst_new  <- substName aa nt2' mv2
             ; e          <- newName nt1
             ; u          <- newName nt2
             ; y          <- newName mv2
             ; u'         <- newName nt2'
             ; x          <- newName mv2'
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s (%s %s %s %s) %s (%s %s %s %s)"
                               e u u' x y
                               (neq x y mv2 mv2')
                               subst_out u y subst_in u' x e
                               subst_in subst_new u y u' x subst_out u y e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | canBindIn aa nt2' nt2 =
          do { subst_out  <- substName aa nt1 mv2
             ; subst_in   <- substName aa nt1 mv2'
             ; fv_fn      <- fvName aa nt2 mv2'
             ; e          <- newName nt1
             ; u          <- newName nt2
             ; y          <- newName mv2
             ; u'         <- newName nt2'
             ; x          <- newName mv2'
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s %s %s (%s %s %s %s)"
                               e u u' x y
                               x mvSetNotin fv_fn u
                               (neq x y mv2 mv2')
                               subst_out u y subst_in u' x e
                               subst_in u' x subst_out u y e
             }

      thm aa nt1 nt2 mv2 nt2' mv2' | otherwise =
          do { subst_out  <- substName aa nt1 mv2
             ; subst_in   <- substName aa nt1 mv2'
             ; e          <- newName nt1
             ; u          <- newName nt2
             ; y          <- newName mv2
             ; u'         <- newName nt2'
             ; x          <- newName mv2'
             ; return $ printf "forall %s %s %s %s %s,\n\
                               \  %s %s %s %s ->\n\
                               \%s\
                               \  %s %s %s (%s %s %s %s) = %s %s %s (%s %s %s %s)"
                               e u u' x y
                               (neq x y mv2 mv2')
                               subst_out u y subst_in u' x e
                               subst_in u' x subst_out u y e
             }
