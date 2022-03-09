{-# LANGUAGE FlexibleContexts #-}

module CoqLNOutputThmLc where


import Data.Maybe  ( catMaybes )
import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators
import MyLibrary ( sepStrings )

lcThms :: ASTAnalysis -> [[NtRoot]] -> M String
lcThms aa nts =
    do { degree_of_lcs     <- mapM (local . degree_of_lc aa) nts
       ; lc_bodys          <- mapM (local . lc_body aa) nts
       ; lc_body_constrs   <- mapM (local . lc_body_constr aa) nts
       ; lc_existss        <- mapM (local . lc_exists aa) nts
       ; lc_exists_hints   <- mapM (local . lc_exists_hint aa) nts
       ; lc_exists_tactics <- mapM (local . lc_exists_tactic aa) nts
       ; lc_of_degrees     <- mapM (local . lc_of_degree aa) nts
       ; lc_of_lc_sets     <- mapM (local . lc_of_lc_set aa) nts
       ; lc_set_of_lcs     <- mapM (local . lc_set_of_lc aa) nts
       ; lc_uniques        <- mapM (local . lc_unique aa) nts
       ; return $ printf "Ltac %s ::= auto with %s %s; tauto.\n\
                         \Ltac %s ::= autorewrite with %s.\n\
                         \\n"
                         defaultAuto hintDb bruteDb
                         defaultAutoRewr hintDb ++
                  concat degree_of_lcs ++
                  concat lc_of_degrees ++
                  concat lc_exists_tactics ++
                  (concat $ concat lc_existss) ++
                  (concat $ concat lc_exists_hints) ++
                  concat lc_bodys ++
                  (concat $ concat lc_body_constrs) ++
                  concat lc_uniques ++
                  concat lc_of_lc_sets ++
                  concat lc_set_of_lcs ++ "\n"
       }

{- | @degree 0 e@ when @lc e@. -}

degree_of_lc :: ASTAnalysis -> [NtRoot] -> M String
degree_of_lc aaa nt1s =
    do { thms  <- processNt1Nt2Mv2 aaa nt1s thm
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; types <- processNt1 aaa nt1s lcName
       ; h1    <- newName "H"
       ; h2    <- newName "H"
       ; freshTacs <- genFreshTacs
       ; let proof = printf "%s\
                            \intros;\n\
                            \%s\
                            \repeat (match goal with\n\
                            \          | %s : _, %s : _ |- _ => specialize %s with %s\n\
                            \        end);\n\
                            \%s; eauto with %s."
                            (mutPfStart Prop types)
                            (concat freshTacs :: String)
                            h1 h2 h1 h2
                            defaultSimp hintDb
       ; mutualLemmaText2 Resolve NoRewrite NoHide [hintDb] Prop names thms (repeat proof)
       }
    where
      name aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; lc     <- lcName aa nt1
             ; return $ degree ++ "_of_" ++ lc
             }

      thm aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; lc     <- lcName aa nt1
             ; e1     <- newName nt1
             ; return $ printf "forall %s,\n\
                               \  %s %s ->\n\
                               \  %s 0 %s"
                               e1
                               lc e1
                               degree e1
             }

      genFreshTacs =
          sequence $
          do { nt2 <- filter (canBindOver aaa (head nt1s)) (ntRoots aaa)
             ; mv2 <- mvsOfNt aaa nt2
             ; return $ do { x   <- newName mv2
                           ; return $ printf
                             "let %s := fresh \"%s\" in %s %s;\n"
                             x x pickFreshTac x
                           }
             }

{- | @lc (open e u)@ when @body e@ and @lc u@. -}

lc_body :: ASTAnalysis -> [NtRoot] -> M String
lc_body aaa nt1s =
    do { gens  <- processNt1Nt2Mv2 aaa nt1s gen
       ; names <- processNt1Nt2Mv2 aaa nt1s name
       ; lemmaText2 Resolve NoRewrite NoHide [hintDb] names gens
       }
    where
      name aa nt1 _ mv2 =
          do { body <- bodyName aa nt1 mv2
             ; return $ "lc_" ++ body
             }

      gen aa nt1 nt2 mv2 =
          do { body      <- bodyName aa nt1 mv2
             ; existsTac <- lc_exists_tacticName aa nt1s
             ; lc        <- lcName aa nt1
             ; lc'       <- lcName aa nt2
             ; open      <- openName aa nt1 mv2
             ; e         <- newName nt1
             ; u         <- newName nt2
             ; x         <- newName mv2
             -- ORDER TO OPEN
             ; let stmt = printf "forall %s %s,\n\
                                 \  %s %s ->\n\
                                 \  %s %s ->\n\
                                 \  %s (%s %s %s)"
                                 e u
                                 body e
                                 lc' u
                                 lc open e u
             ; let proof = printf "unfold %s;\n\
                                  \%s;\n\
                                  \let %s := fresh \"x\" in\n\
                                  \%s %s;\n\
                                  \%s %s;\n\
                                  \%s;\n\
                                  \eauto with %s."
                                  body
                                  defaultSimp
                                  x
                                  pickFreshTac x
                                  specializeAllTac x
                                  existsTac
                                  hintDb
             ; return (stmt, proof)
             }

{- | @body u@ when @lc (C ... u ...)@. -}

lc_body_constr :: ASTAnalysis -> [NtRoot] -> M [String]
lc_body_constr aaa nt1s =
    sequence $ do { nt1                      <- nt1s
                  ; (Syntax _ _ cs)          <- [runM [] $ getSyntax aaa nt1]
                  ; c@(SConstr _ _ _ args _) <- [c | c <- cs, hasBindingArg c]
                  ; let nargs = zip args [1..]
                  ; (a, n)                   <- [(a, n) | (a, n) <- nargs, hasBindingArg a]
                  ; return $ local $ thm aaa nt1 c a n
                  }
    where
      thm aa nt1 c@(SConstr _ _ _ args _) (BindingArg mv _ nt') n =
          do { body <- bodyName aa nt' mv
             ; lc <- lcName aa nt1
             ; arg_names <- mapM newName (map toRoot args)
             ; let dist_arg = arg_names !! (n - 1)
             ; let stmt = printf "forall %s,\n\
                                 \  %s (%s %s) ->\n\
                                 \  %s %s"
                                 (sepStrings " " arg_names)
                                 lc (toName c) (sepStrings " " arg_names)
                                 body dist_arg
             ; let proof = defaultSimp ++ "."
             ; let name = "lc_body_" ++ (toName c) ++ "_" ++ (show n)
             ; lemmaText Resolve NoRewrite NoHide [hintDb] name stmt proof
             }

      thm _ _ _ _ _ = error "Internal error (lc_body_constr)."

{- | "Existential" constructors for @lc@. -}

lc_exists :: ASTAnalysis -> [NtRoot] -> M [String]
lc_exists aaa nt1s =
    sequence $ do { nt1             <- nt1s
                  ; (Syntax _ _ cs) <- [runM [] $ getSyntax aaa nt1]
                  ; c               <- [c | c <- cs, hasBindingArg c]
                  ; return $ local $ thm aaa nt1 c
                  }
    where
      thm aa nt1 c@(SConstr pos _ _ args _) =
          do { lc     <- lcName aa nt1
             ; glomps <- mapM (glomp aa pos) args
             ; let (mvs, nts, hyps) = unzip3 glomps
             ; let stmt  = printf "forall %s %s,\n\
                                  \%s\
                                  \  %s (%s %s)"
                                  (sepStrings " " $ catMaybes mvs) (sepStrings " " nts)
                                  (concat (catMaybes hyps) :: String)
                                  lc (toName c) (sepStrings " " nts)
             ; base <- lcConstrName c
             ; tac  <- lc_exists_tacticName aa nt1s
             ; let name  = base ++ "_exists"
             ; let proof = printf "intros; %s; eauto with %s." tac hintDb
             ; lemmaText NoResolve NoRewrite NoHide [hintDb] name stmt proof
             }

      glomp _ pos IndexArg = error $ show pos ++ ": Internal error (lc_exists / IndexArg)."

      glomp _ _ (MvArg mv) =
          do { n <- newName mv
             ; return $ (Nothing, n, Nothing)
             }

      glomp aa _ (NtArg nt)
          | isOpenable aa nt =
              do { n  <- newName nt
                 ; lc <- lcName aa nt
                 ; return $ (Nothing, n, Just (printf "  %s %s ->\n" lc n))
                 }
          | otherwise =
              do { n <- newName nt
                 ; return $ (Nothing, n, Nothing)
                 }

      glomp aa _ (BindingArg mv' nt' nt) =
          do { n       <- newName nt
             ; x       <- newName mv'
             ; lc      <- lcName aa nt
             ; open_fn <- openName aa nt mv'
             ; constr  <- getFreeVarConstr aa nt' mv'
             -- ORDER TO OPEN
             ; return $ (Just x, n, Just (printf "  %s (%s %s (%s %s)) ->\n"
                                                 lc open_fn n (toName constr) x))
             }

{- | Hints for the "existential" constructors for @lc@. -}

lc_exists_hint :: ASTAnalysis -> [NtRoot] -> M [String]
lc_exists_hint aaa nt1s =
    sequence $ do { nt1             <- nt1s
                  ; (Syntax _ _ cs) <- [runM [] $ getSyntax aaa nt1]
                  ; c               <- [c | c <- cs, hasBindingArg c]
                  ; return $ local $ thm aaa nt1 c
                  }
    where
      thm aa nt1 c@(SConstr _ _ _ args _) =
          do { lc       <- lcName aa nt1
             ; lcConstr <- lcConstrName c
             ; let bargs = filter hasBindingArg args
             ; picks <- local $ mapM pick bargs
             ; names <- local $ mapM name bargs
             ; return $ printf "#[export] Hint Extern 1 (%s (%s%s)) =>\n\
                               \%s\
                               \  apply (%s%s) : core.\n\
                               \\n"
                               lc (toName c) (sepStrings " " ("":map (\_ -> "_") args))
                               (concat picks :: String)
                               (lcConstr ++ "_exists") (sepStrings " " ("":names))
             }

      pick (BindingArg mv _ _) =
          do { n <- newName mv
             ; return $ printf "  let %s := fresh in\n\
                               \  pick_fresh %s;\n"
                               n n
             }

      pick _ = error "Internal error (lc_exists_hint)."

      name (BindingArg mv _ _) = newName mv

      name _ = error "Internal error (lc_exists_hint)."

{- | @lc e@ when @lc_set e@. -}

lc_of_lc_set :: ASTAnalysis -> [NtRoot] -> M String
lc_of_lc_set aaa nt1s =
    if not (isOpenable aaa (head nt1s))
    then return ""
    else
    do { thms     <- processNt1 aaa nt1s thm
       ; names    <- processNt1 aaa nt1s name
       ; types    <- processNt1 aaa nt1s lcSetName
       ; let proof = mutPfStart Prop types ++ defaultSimp ++ "."
       ; mutualLemmaText Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 =
          do { lc    <- lcName aa nt1
             ; lcSet <- lcSetName aa nt1
             ; return $ lc ++ "_of_" ++ lcSet
             }

      thm aa nt1 =
          do { e     <- newName nt1
             ; lc    <- lcName aa nt1
             ; lcSet <- lcSetName aa nt1
             ; return $ printf "forall %s, %s %s -> %s %s"
                               e lcSet e lc e
             }

{- | @degree 0 e@ implies @lc e@.

   Implementation note (BEA): This theorem is downright painful.  Due
   to its structure, we need to assemble everything by hand.  Consider
   making \"size induction\" its own combinator, maybe? -}

lc_of_degree :: ASTAnalysis -> [NtRoot] -> M String
lc_of_degree aaa nt1s =
    if not (isOpenable aaa (head nt1s))
    then return ""
    else
    do { i     <- newName "i"
       ; h     <- newName "H"
       ; thms  <- processNt1 aaa nt1s (thm i)
       ; names <- processNt1 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let mut_name = sepStrings "_" names ++ "_size_mutual"
       ; let mut_stms = printf "forall %s,\n%s" i (sepStrings " /\\\n" $ map wrap thms)
       ; let proof = printf "intros %s; pattern %s; apply %s;\n\
                            \clear %s; intros %s %s;\n\
                            \%s\
                            \%s;\n\
                            \(* non-trivial cases *)\n\
                            \constructor; %s; %s;\n\
                            \(* instantiate the size *)\n\
                            \match goal with\n\
                            \  | |- _ = _ => reflexivity\n\
                            \  | _ => idtac\n\
                            \end;\n\
                            \instantiate;\n\
                            \(* everything should be easy now *)\n\
                            \%s."
                            i i ltWfRec
                            i i h
                            (mutPfStart Prop types) defaultSimp
                            defaultSimp eapplyFirst
                            defaultSimp
       ; gens <- processNt1 aaa nt1s (gen mut_name)
       ; s1 <- lemmaText  NoResolve NoRewrite Hide [] mut_name mut_stms proof
       ; s2 <- lemmaText2 Resolve NoRewrite NoHide [hintDb] [names] [gens]
       ; return $ s1 ++ s2
       }
    where
      wrap s = "(" ++ s ++ ")"

      name aa nt1 =
          do { lc <- lcName aa nt1
             ; return $ lc ++ "_of_degree"
             }

      thm i aa nt1 =
          do { e    <- newName nt1
             ; lc   <- lcName aa nt1
             ; size <- sizeName aa nt1
             ; hyps <- processNt1Nt2Mv2 aa [nt1] (hyp e)
             ; return $ printf "forall %s,\n\
                               \  %s %s = %s ->\n\
                               \%s\
                               \  %s %s"
                               e
                               size e i
                               (concat $ concat hyps)
                               lc e
             }

      hyp e aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; return $ "  " ++ degree ++ " 0 " ++ e ++ " ->\n"
             }

      gen n aa nt1 =
          do { e    <- newName nt1
             ; lc   <- lcName aa nt1
             ; hyps <- processNt1Nt2Mv2 aa [nt1] (hyp e)
             ; size <- sizeName aa nt1
             ; let stmt = printf "forall %s,\n\
                                 \%s\
                                 \  %s %s"
                                 e
                                 (concat $ concat hyps)
                                 lc e
             ; let proof = printf "intros %s; intros;\n\
                                  \pose proof (%s (%s %s));\n\
                                  \intuition eauto."
                                  e
                                  n size e
             ; return (stmt, proof)
             }

{- | @lc e@ implies @lc_set e@.

   Implementation note (BEA): This theorem is downright painful.  Due
   to its structure, we need to assemble everything by hand.  Consider
   making \"size induction\" its own combinator, maybe? -}

lc_set_of_lc :: ASTAnalysis -> [NtRoot] -> M String
lc_set_of_lc aaa nt1s =
    if not (isOpenable aaa (head nt1s))
    then return ""
    else
    do { i      <- newName "i"
       ; h      <- newName "H"
       ; thms   <- processNt1 aaa nt1s (thm i)
       ; names  <- processNt1 aaa nt1s name
       ; types  <- processNt1 aaa nt1s ntType
       ; lemmas <- mapM (name aaa)
                   (concatMap
                     (\nt -> filter (flip (isSubordTo aaa) nt) (ntRoots aaa))
                     nt1s)
       ; let mut_name = sepStrings "_" names ++ "_size_mutual"
       ; let mut_stms = printf "forall %s,\n%s" i (sepStrings " *\n" $ map wrap thms)
       ; let proof = printf "intros %s; pattern %s; apply %s;\n\
                            \clear %s; intros %s %s;\n\
                            \%s\
                            \%s;\n\
                            \try solve [assert False by %s; tauto];\n\
                            \(* non-trivial cases *)\n\
                            \constructor; %s;\n\
                            \try first [%s];\n\
                            \%s; %s;\n\
                            \(* instantiate the size *)\n\
                            \match goal with\n\
                            \  | |- _ = _ => reflexivity\n\
                            \  | _ => idtac\n\
                            \end;\n\
                            \instantiate;\n\
                            \(* everything should be easy now *)\n\
                            \%s."
                            i i ltWfRec
                            i i h
                            (mutPfStart Set types) defaultSimp
                            defaultSimp
                            defaultSimp
                            (sepStrings "\n | " $ map ("apply " ++) lemmas)
                            defaultSimp eapplyFirst
                            defaultSimp
       ; gens <- processNt1 aaa nt1s (gen mut_name)
       ; s1 <- lemmaText  NoResolve NoRewrite Hide [] mut_name mut_stms proof
       ; s2 <- lemmaText2 Resolve NoRewrite NoHide [hintDb] [names] [gens]
       ; return $ s1 ++ s2
       }
    where
      wrap s = "(" ++ s ++ ")"

      name aa nt1 =
          do { lc    <- lcName aa nt1
             ; lcSet <- lcSetName aa nt1
             ; return $ lcSet ++ "_of_" ++ lc
             }

      thm i aa nt1 =
          do { e     <- newName nt1
             ; lc    <- lcName aa nt1
             ; lcSet <- lcSetName aa nt1
             ; size  <- sizeName aa nt1
             ; return $ printf "forall %s,\n\
                               \  %s %s = %s ->\n\
                               \  %s %s ->\n\
                               \  %s %s"
                               e
                               size e i
                               lc e
                               lcSet e
             }

      gen n aa nt1 =
          do { e     <- newName nt1
             ; lc    <- lcName aa nt1
             ; lcSet <- lcSetName aa nt1
             ; size  <- sizeName aa nt1
             ; let stmt = printf "forall %s,\n\
                                 \  %s %s ->\n\
                                 \  %s %s"
                                 e
                                 lc e
                                 lcSet e
             ; let proof = printf "intros %s; intros;\n\
                                  \pose proof (%s (%s %s));\n\
                                  \intuition eauto."
                                  e
                                  n size e
             ; return (stmt, proof)
             }

{- | @(pf1 pf2 : lc e) -> pf1 = pf2@. -}

lc_unique :: ASTAnalysis -> [NtRoot] -> M String
lc_unique aaa nt1s =
    if not (isOpenable aaa (head nt1s))
    then return ""
    else
    do { pf       <- newName "proof"
       ; thms     <- processNt1 aaa nt1s thm
       ; names    <- processNt1 aaa nt1s name
       ; types    <- processNt1 aaa nt1s lcName
       ; let proof = mutPfStart Prop types ++
                     printf "intros;\n\
                            \let %s := fresh \"%s\" in\n\
                            \%s %s; dependent destruction %s;\n\
                            \f_equal; %s; auto using %s with %s."
                            pf pf
                            renameLastTac pf pf
                            defaultSimp funExtEq hintDb
       ; mutualLemmaText Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 =
          do { lc <- lcName aa nt1
             ; return $ lc ++ "_unique"
             }

      thm aa nt1 =
          do { e   <- newName nt1
             ; lc  <- lcName aa nt1
             ; pf1 <- newName "proof"
             ; pf2 <- newName "proof"
             ; return $ printf "forall %s (%s %s : %s %s), %s = %s"
                               e pf1 pf2 lc e pf1 pf2
             }

{- | Generates tactics for the lc_exists theorems. -}

lc_exists_tactic :: ASTAnalysis -> [NtRoot] -> M String
lc_exists_tactic aaa nt1s =
    do { ls  <- processNt1 aaa nt1s f
       ; tac <- lc_exists_tacticName aaa nt1s
       ; return $ printf "Ltac %s :=\n\
                         \  repeat (match goal with\n\
                         \%s\
                         \          end).\n\
                         \\n"
                         tac
                         (concatMap g  $ map (sepStrings ";\n              ") ls)
       }
    where
      g x = "            | H : _ |- _ =>\n              "
            ++ x
            ++ (if null x then "fail 1\n" else "; clear H\n")

      f aa nt1 =
          sequence $
          do { nt2 <- filter (canBindOver aa nt1) (ntRoots aa)
             ; mv2 <- mvsOfNt aa nt2
             ; return $ do { n <- name aa nt1 nt2 mv2
                           ; j <- newName "J"
                           ; return $
                             printf "let %s := fresh in pose proof H as %s; apply %s in %s"
                                    j j n j
                           }
             }

      name aa nt1 _ mv2 =
          do { degree <- degreeName aa nt1 mv2
             ; lc     <- lcName aa nt1
             ; return $ degree ++ "_of_" ++ lc
             }

{- | Generates tactics for the lc_exists theorems. -}

lc_exists_tacticName :: ASTAnalysis -> [NtRoot] -> M String
lc_exists_tacticName aaa nt1s =
    do { types <- processNt1 aaa nt1s ntType
       ; return $ sepStrings "_" types ++ "_lc_exists_tac"
       }
