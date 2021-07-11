{-# LANGUAGE FlexibleContexts #-}

{- | Implementation notes (BEA): The exported function expect that the
   given list of 'NtRoot's all be canonical and correspond to a
   collection of mutually declared non-terminals. -}

module CoqLNOutputDefinitions
    ( processBody
    , processClose
    , processDegree
    , processLc
    , processNt
    , processSize
    , processSwap
    , processTactics
    ) where

import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCombinators
import CoqLNOutputCommon
import MyLibrary ( mapMM, sepStrings )


{- ----------------------------------------------------------------------- -}
{- * Assorted helper functions -}

{- | Constructs the @Scheme@ declarations for the given list of types
   at the sort @Prop@. -}

schemeIndDecl :: [Name] -> Int -> M Name
schemeIndDecl ns i =
    do { hyps <- sequence $ take (i + length ns) $ repeat (newName "H")
       ; let args  = sepStrings " " hyps
       ; let calls = map (\s -> s ++ " " ++ args) $ map schemeIndName ns
       ; return $ printf
         "Scheme %s.\n\
         \\n\
         \Definition %s :=\n\
         \  fun %s =>\n\
         \  %s.\n\
         \\n"
         (sepStrings "\n  with " (map f ns))
         (mutIndName ns) args (foldr1 join calls)
       }
    where
      join = printf "(conj (%s)\n  (%s))"

      f n = printf "%s := Induction for %s Sort Prop" (schemeIndName n) n

{- | Constructs the @Scheme@ declarations for the given list of types
   at the sort @Set@. -}

schemeRecDecl :: [Name] -> Int -> M Name
schemeRecDecl ns i =
    do { hyps <- sequence $ take (i + length ns) $ repeat (newName "H")
       ; let args  = sepStrings " " hyps
       ; let calls = map (\s -> s ++ " " ++ args) $ map schemeRecName ns
       ; return $ printf
         "Scheme %s.\n\
         \\n\
         \Definition %s :=\n\
         \  fun %s =>\n\
         \  %s.\n\
         \\n"
         (sepStrings "\n  with " (map f ns))
         (mutRecName ns) args (foldl1 join calls)
       }
    where
      join = printf "(pair (%s)\n  (%s))"

      f n = printf "%s := Induction for %s Sort Set" (schemeRecName n) n


{- ----------------------------------------------------------------------- -}
{- * Output for @body@ -}

processBody :: ASTAnalysis -> [NtRoot] -> M String
processBody aaa nt1s =
    do { defs  <- processNt1Nt2Mv2 aaa nt1s f
       ; hints <- processNt1Nt2Mv2 aaa nt1s g
       ; return $ (concat $ concat defs) ++
                  (concat $ concat hints)
       }
    where
      f aa nt1 nt2 mv2 =
          do { body   <- bodyName aa nt1 mv2
             ; lc     <- lcName aa nt1
             ; open   <- openName aa nt1 mv2
             ; constr <- getFreeVarConstr aa nt2 mv2
             ; e      <- newName nt1
             ; x      <- newName mv2
             -- ORDER TO OPEN
             ; return $ printf
               "Definition %s %s := forall %s, %s (%s %s (%s %s)).\n\n"
               body e
               x lc open e (toName constr) x
             }

      g aa nt1 _ mv2 =
          do { body <- bodyName aa nt1 mv2
             ; return $ "#[global] Hint Unfold " ++ body ++ " : core.\n\n"
             }


{- ----------------------------------------------------------------------- -}
{- * Output for @close@ -}

{- | Generates the text for the @close@ and @close_rec@ functions. -}

processClose :: ASTAnalysis -> [NtRoot] -> M String
processClose aa nts =
    do { s1 <- processCloseRecs aa nts
       ; s2 <- processCloseDefs aa nts
       ; return $ s1 ++ s2
       }

{- | Generates the text for the definitions of @close@. -}

processCloseDefs :: ASTAnalysis -> [NtRoot] -> M String
processCloseDefs aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ concat ss
       }
    where
      f aa nt1 _ mv2 =
          do { fn    <- closeName aa nt1 mv2
             ; fnrec <- closeRecName aa nt1 mv2
             ; e     <- newName nt1
             ; x     <- newName mv2
             ; return $ printf
               "Definition %s %s %s := %s 0 %s %s.\n\n"
               fn x e fnrec x e
             }

{- | Generates the text for the definitions of @close_rec@. -}

processCloseRecs :: ASTAnalysis -> [NtRoot] -> M String
processCloseRecs aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ map join $ ss
       }
    where
      join strs = printf "Fixpoint %s.\n\n" (sepStrings "\n\nwith " strs)

      f aa nt1 nt2 mv2 =
        do { close           <- closeRecName aa nt1 mv2
           ; k               <- newName bvarRoot
           ; x               <- newName mv2
           ; xtype           <- mvType aa mv2
           ; e               <- newName nt1
           ; etype           <- ntType aa nt1
           ; (Syntax _ _ cs) <- getSyntax aa nt1
           ; branches        <- mapM (local . branch k x nt1 nt2 mv2) cs
           ; return $ printf
             "%s (%s : %s) (%s : %s) (%s : %s) {struct %s} : %s :=\n\
             \  match %s with\n\
             \%s\n\
             \  end"
             close k bvarType x xtype e etype e etype
             e
             (sepStrings "\n" branches)
            }

      branch k _ nt1 nt2 mv2 c@(SConstr _ _ _ _ (Bound mv'))
          | canonRoot aaa nt1 == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
                do { n <- newName bvarRoot
                   ; return $ printf
                     "    | %s %s => if (%s %s %s) then (%s %s) else (%s %s)"
                     (toName c) n
                     bvarLtGeDec n k
                     (toName c) n
                     (toName c) ("(S " ++ n ++ ")")
                   }

      branch k x nt1 nt2 mv2 c@(SConstr _ _ _ _ (Free mv'))
                | canonRoot aaa nt1 == canonRoot aaa nt2 &&
                  canonRoot aaa mv2 == canonRoot aaa mv' =
              do { y   <- newName mv2
                 ; bsc <- getBoundVarConstr aaa nt1 mv2
                 ; return $ printf
                   "    | %s %s => if (%s == %s) then (%s %s) else (%s %s)"
                   (toName c) y
                   x y
                   (toName bsc) k
                   (toName c) y
                 }
      branch k x nt1 nt2 mv2 c@(SConstr _ _ _ ts _) =
          do { args  <- mapM (newName . toRoot) ts
             ; calls <- mapM (call k x nt1 nt2 mv2) (zip ts args)
             ; return $ printf
               "    | %s%s => %s%s"
               (toName c)
               (sepStrings " " ("" : args))
               (toName c)
               (sepStrings " " ("" : calls))
             }

      call _ _ _ _ _ (IndexArg, z) = return z
      call _ _ _ _ _ (MvArg _,  z) = return z

      call k x _ nt2 mv2 (NtArg nt, z)
          | canBindIn aaa nt2 nt =
              do { fn <- closeRecName aaa nt mv2
                 ; return $ printf "(%s %s %s %s)" fn k x z
                 }
          | otherwise =
              return z

      call k x nt1 nt2 mv2 (BindingArg mv' ntm nt, z)
          | canonRoot aaa ntm == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
                do { fn <- closeRecName aaa nt mv2
                   ; return $ printf
                     "(%s %s %s %s)"
                     fn ("(S " ++ k ++ ")") x z
                   }
          | otherwise =
              call k x nt1 nt2 mv2 (NtArg nt, z)


{- ----------------------------------------------------------------------- -}
{- * Output for @degree@ -}

{- | Generates the text for the @degree@ predicates. -}

processDegree :: ASTAnalysis -> [NtRoot] -> M String
processDegree aa nts =
    do { s1 <- processDegreeDefs aa nts
       ; s2 <- processDegreeSchemes aa nts
       ; s3 <- processDegreeHints aa nts
       ; return $ s1 ++ s2 ++ s3
       }

{- | Generates the @Scheme@ declarations for @degree@. -}

processDegreeSchemes :: ASTAnalysis -> [NtRoot] -> M String
processDegreeSchemes aaa nt1s =
    do { ss      <- processNt1Nt2Mv2 aaa nt1s f
       -- ; ssSet   <- processNt1Nt2Mv2 aaa nt1s g
       ; countss <- processNt1Nt2Mv2 aaa nt1s count
       ; let counts = map sum countss
       ; s1 <- mapM (\(n,i) -> local $ schemeIndDecl n i) (zip ss counts)
       -- ; s2 <- mapM (\(n,i) -> local $ schemeIndDecl n i) (zip ssSet counts)
       -- ; s3 <- mapM (\(n,i) -> local $ schemeRecDecl n i) (zip ssSet counts)
       ; return $ concat s1 -- ++ concat s2 ++ concat s3
       }
    where
      f aa nt1 _ mv2 = degreeName aa nt1 mv2
      -- g aa nt1 _ mv2 = degreeSetName aa nt1 mv2

      count aa nt1 _ _ =
          do { (Syntax _ _ cs) <- getSyntax aa nt1
             ; return $ length cs
             }

{- | Generates the @Hint@ declarations for the @degree@ predicates. -}

processDegreeHints :: ASTAnalysis -> [NtRoot] -> M String
processDegreeHints aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ concat $ ss
       }
    where
      f aa nt1 _ mv2 =
          do { names1 <- degreeName aa nt1 mv2
             -- ; names2 <- degreeSetName aa nt1 mv2
             ; return $ printf
               "#[global] Hint Constructors %s : core %s.\n\n"
               names1 hintDb
             }

{- | Generates the text for the @degree@ predicates. -}

processDegreeDefs :: ASTAnalysis -> [NtRoot] -> M String
processDegreeDefs aaa nt1s =
    do { ss1 <- processNt1Nt2Mv2 aaa nt1s (f Prop)
       -- ; ss2 <- processNt1Nt2Mv2 aaa nt1s (f Set)
       ; return $ (concat $ map join ss1) -- ++ (concat $ map join ss2)
       }
    where
      join strs = printf "Inductive %s.\n\n" (sepStrings "\n\nwith " strs)

      degree Prop = degreeName
      degree Set  = degreeSetName

      degreeConstr Prop = degreeConstrName
      degreeConstr Set  = degreeSetConstrName

      f sort aa nt1 nt2 mv2 =
          do { (Syntax _ _ cs) <- getSyntax aa nt1
             ; degname         <- degree sort aa nt1 mv2
             ; nttype          <- ntType aa nt1
             ; cs'             <- mapM (local . constr sort nt1 nt2 mv2) cs
             ; return $ printf
               "%s : %s -> %s -> %s :=\n\
               \%s"
               degname bvarType nttype (show sort)
               (sepStrings "\n" cs')
             }

      constr sort nt1 nt2 mv2 c@(SConstr _ _ _ _ (Bound mv'))
          | canonRoot aaa nt1 == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
                do { deg        <- degree sort aaa nt1 mv2
                   ; deg_constr <- degreeConstr sort aaa c nt1 mv2
                   ; n          <- newName bvarRoot
                   ; i          <- newName bvarRoot
                   ; return $ printf
                     "  | %s : forall %s %s,\n\
                     \    %s %s %s ->\n\
                     \    %s %s (%s %s)"
                     deg_constr n i
                     bvarLt i n
                     deg n (toName c) i
                   }
      constr sort nt1 nt2 mv2 c@(SConstr _ _ _ ts _) =
          do { deg        <- degree sort aaa nt1 mv2
             ; deg_constr <- degreeConstr sort aaa c nt1 mv2
             ; n          <- newName bvarRoot
             ; args       <- mapM (newName . toRoot) ts
             ; hyps       <- mapMM (hyp sort n nt1 nt2 mv2) (zip ts args)
             ; return $ printf
               "  | %s : forall %s,\n\
               \%s\
               \    %s %s (%s%s)"
               deg_constr (sepStrings " " (n : args))
               (concat hyps :: String)
               deg n (toName c) (sepStrings " " ("" : args))
             }

      hyp _ _ _ _ _ (IndexArg , _) = return Nothing
      hyp _ _ _ _ _ (MvArg _,   _) = return Nothing

      hyp sort n _ nt2 mv2 (NtArg ntr, arg)
          | canBindIn aaa nt2 ntr =
              do { deg <- degree sort aaa ntr mv2
                 ; return $ Just $ printf
                   "    %s %s %s ->\n"
                   deg n arg
                 }
          | otherwise =
              return Nothing

      hyp sort n nt1 nt2 mv2 (BindingArg mv' nt' nt'', arg)
          | canonRoot aaa nt' == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
              hyp sort ("(S " ++ n ++")") nt1 nt2 mv2 (NtArg nt'', arg)
          | otherwise =
              hyp sort n nt1 nt2 mv2 (NtArg nt'', arg)


{- ----------------------------------------------------------------------- -}
{- * Output for local closure -}

{- | Generates text for the definitions of @lc@. -}

processLc :: ASTAnalysis -> [NtRoot] -> M String
processLc aa nts' =
    do { let nts = filter (isOpenable aa) nts'
       ; defs         <- mapM def nts
       ; names        <- mapM (lcName aa) nts
       ; namesSet     <- mapM (lcSetName aa) nts
       ; counts       <- mapM count nts
       ; indScheme    <- local $ schemeIndDecl names (sum counts)
       ; indSchemeSet <- local $ schemeIndDecl namesSet (sum counts)
       ; recSchemeSet <- local $ schemeRecDecl namesSet (sum counts)
       ; if null defs
         then return ""
         else return $ printf
              "Inductive %s.\n\
              \\n\
              \%s\
              \%s\
              \%s\
              \%s\
              \%s"
              (sepStrings "\n\nwith " defs)
              indScheme
              indSchemeSet
              recSchemeSet
              (concat (map hint names) :: String)
              (concat (map hint namesSet) :: String)
       }
    where
      count nt1 =
          do { (Syntax _ _ cs) <- getSyntax aa nt1
             ; return $ length $ filter isCountable cs
             }

      isCountable (SConstr _ _ _ _ (Bound _)) = False
      isCountable (SConstr _ _ _ _ _)         = True

      hint = \s -> printf "#[global] Hint Constructors %s : core %s.\n\n" s hintDb

      def :: NtRoot -> M String
      def nt =
          do { (Syntax _ _ cs) <- getSyntax aa nt
             ; lcname          <- lcSetName aa nt
             ; nttype          <- ntType aa nt
             ; cs'             <- mapMM (local . constr nt) cs
             ; return $ printf
               "%s : %s -> Set :=\n\
               \%s"
               lcname nttype
               (sepStrings "\n" cs')
             }

      constr _  (SConstr _ _ _ _ (Bound _)) = return Nothing
      constr nt c@(SConstr _ _ _ ts _)  =
        do { lc        <- lcSetName aa nt
           ; lc_constr <- lcSetConstrName c
           ; args      <- mapM (newName . toRoot) ts
           ; hyps      <- mapMM hyp (zip ts args)
           ; return $ Just $ printf
             "  | %s :%s\n\
             \%s\
             \    %s (%s%s)"
             lc_constr (forallPrefix args)
             (concat hyps :: String)
             lc (toName c) (sepStrings " " ("" : args))
           }
          where
            forallPrefix [] = ""
            forallPrefix xs = " forall " ++ (sepStrings " " xs) ++ ","

            hyp (IndexArg, _) = return Nothing
            hyp (MvArg _,  _) = return Nothing

            hyp (NtArg ntr, arg)
                | isOpenable aa ntr =
                    do { lc <- lcSetName aa ntr
                       ; return $ Just $ printf "    %s %s ->\n" lc arg
                       }
                | otherwise =
                    return Nothing

            hyp (BindingArg mv1 nt1 nt2, arg) =
                do { x        <- newName mv1
                   ; xtype    <- mvType aa mv1
                   ; lc       <- lcSetName aa nt2
                   ; open_fn  <- openName aa nt2 mv1
                   ; fvconstr <- getFreeVarConstr aa nt1 mv1
                   ; return $ Just $ printf
                     "    (forall %s : %s, %s (%s %s (%s %s))) ->\n"
                     x xtype
                     lc
                     open_fn arg (toName fvconstr) x
                   }


{- ----------------------------------------------------------------------- -}
{- * Output for nonterminals -}

{- | Generates text for nonterminal declarations. -}

processNt :: ASTAnalysis -> [NtRoot] -> M String
processNt aa nts =
    do { names     <- mapM (ntType aa) nts
       ; counts    <- mapM count nts
       ; schemeInd <- local $ schemeIndDecl names (sum counts)
       ; schemeRec <- local $ schemeRecDecl names (sum counts)
       ; return $ printf "%s%s"
         schemeInd
         schemeRec
       }
    where
      count nt1 =
          do { (Syntax _ _ cs) <- getSyntax aa nt1
             ; return $ length cs
             }

{- BEA: Subsumed by Ott.
{- | Generates the \"core\" text for nonterminal declarations. -}

coreNtText :: ASTAnalysis -> NtRoot -> M String
coreNtText aa nt =
    do { t               <- ntType aa nt
       ; (Syntax _ _ cs) <- getSyntax aa nt
       ; cs'             <- mapM constr cs
       ; return $ t ++ " : Set :=\n" ++ sepStrings "\n" cs'
       }
    where
      constr c@(SConstr _ _ _ ts _) =
          do { args   <- mapM text ts
             ; result <- ntType aa nt
             ; return $ "  | " ++ (toName c) ++ " : " ++
                        sepStrings " -> " (args ++ [result])
             }

      text (IndexArg)         = return bvarType
      text (MvArg x)          = mvType aa x
      text (NtArg x)          = ntType aa x
      text (BindingArg _ _ x) = ntType aa x
-}


{- ----------------------------------------------------------------------- -}
{- * Output for @size@ -}

{- | Generates the text for the @size@ functions. -}

processSize :: ASTAnalysis -> [NtRoot] -> M String
processSize aa nts =
    do { defs <- mapM (local . def) nts
       ; return $ printf "Fixpoint %s.\n\n" (sepStrings "\n\nwith " defs)
       }
    where
      def nt =
          do { size_fn         <- sizeName aa nt
             ; e               <- newName nt
             ; etype           <- ntType aa nt
             ; (Syntax _ _ cs) <- getSyntax aa nt
             ; branches        <- mapM (local . branch) cs
             ; return $ printf
               "%s (%s : %s) {struct %s} : nat :=\n\
               \  match %s with\n\
               \%s\n\
               \  end"
               size_fn e etype e
               e
               (sepStrings "\n" branches)
             }

      branch c@(SConstr _ _ _ ts _) =
          do { args  <- mapM (newName . toRoot) ts
             ; calls <- mapMM call (zip ts args)
             ; return $ printf "    | %s%s => 1%s"
                      (toName c)
                      (sepStrings " " ("" : args))
                      (sepStrings " + " ("" : calls))
             }

      call (IndexArg,          _) = return Nothing
      call (MvArg _,           _) = return Nothing
      call (BindingArg _ _ nt, z) = call (NtArg nt, z)

      call (NtArg nt, z) =
          do { fn <- sizeName aa nt
             ; return $ Just $ printf "(%s %s)" fn z
             }


{- ----------------------------------------------------------------------- -}
{- * Swapping -}

{- | Generates text for the @swap@ functions. -}

processSwap :: ASTAnalysis -> [NtRoot] -> M String
processSwap aaa nt1s =
    do { defs <- processNt1 aaa nt1s def
       ; return $ "Fixpoint " ++ (sepStrings "\n\nwith " defs) ++ ".\n\n"
       }
    where
      def aa nt =
          do { swap_fn         <- swapImplName aa nt
             ; ab              <- newName "ab"
             ; e               <- newName nt
             ; etype           <- ntType aa nt
             ; (Syntax _ _ cs) <- getSyntax aa nt
             ; branches        <- mapM (local . branch ab) cs
             ; return $ printf
               "%s (%s : %s * %s) (%s : %s) {struct %s} : %s :=\n\
               \  match %s with\n\
               \%s\n\
               \  end"
               swap_fn ab atomType atomType e etype e etype
               e
               (sepStrings "\n" branches)
             }

      branch ab c@(SConstr _ _ _ ts _) =
          do { args  <- mapM (newName . toRoot) ts
             ; calls <- mapM (call ab) (zip ts args)
             ; return $ printf "    | %s%s => %s%s"
                      (toName c)
                      (sepStrings " " ("" : args))
                      (toName c)
                      (sepStrings " " ("" : calls))
             }

      call _  (IndexArg,          z) = return z
      call ab (BindingArg _ _ nt, z) = call ab (NtArg nt, z)

      call ab (MvArg _,          z) =
          return $ printf "(%s %s %s)" swapName ab z

      call ab (NtArg nt, z) =
          do { fn <- swapImplName aaa nt
             ; return $ printf "(%s %s %s)" fn ab z
             }


{- ----------------------------------------------------------------------- -}
{- * Tactic support -}

{- | Generates the text for all supporting tactics. -}

processTactics :: ASTAnalysis -> M String
processTactics _ =
    do { return $ printf
         "(** Additional hint declarations. *)\n\
         \\n\
         \#[global] Hint Resolve @plus_le_compat : %s.\n\
         \\n\
         \(** Redefine some tactics. *)\n\
         \\n\
         \Ltac default_case_split ::=\n\
         \  first\n\
         \    [ progress destruct_notin\n\
         \    | progress destruct_sum\n\
         \    | progress safe_f_equal\n\
         \    ].\n\
         \\n"
         hintDb
       }
