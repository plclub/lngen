{- ----------------------------------------------------------------------- -}
{- * Output for substitution -}

{- | Generates text for the @subst@ functions. -}

processSubst :: ASTAnalysis -> [NtRoot] -> M String
processSubst aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ map join ss
       }
    where
      join strs = printf "Fixpoint %s.\n\n" (sepStrings "\n\nwith " strs)

      f aa nt1 nt2 mv2 =
          do { subst_fn        <- substName aa nt1 mv2
             ; x               <- newName mv2
             ; xtype           <- mvType aa mv2
             ; u               <- newName nt2
             ; utype           <- ntType aa nt2
             ; e               <- newName nt1
             ; etype           <- ntType aa nt1
             ; (Syntax _ _ cs) <- getSyntax aa nt1
             ; branches        <- mapM (local . branch nt1 nt2 mv2 x u) cs
             ; return $ printf
               "%s (%s : %s) (%s : %s) (%s : %s) {struct %s} : %s :=\n\
               \  match %s with\n\
               \%s\n\
               \  end"
               subst_fn u utype x xtype e etype e etype
               e
               (sepStrings "\n" branches)
             }

      branch nt1 nt2 mv2 x u c@(SConstr _ _ _ _ (Free mv'))
          | canonRoot aaa nt1 == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
                do { y   <- newName mv2
                   ; return $ printf
                     "    | %s %s => if (%s == %s) then (%s) else (%s %s)"
                     (toName c) y
                     x y
                     u
                     (toName c) y
                   }
      branch _ nt2 mv2 x u c@(SConstr _ _ _ ts _) =
          do { args  <- mapM (newName . toRoot) ts
             ; calls <- mapM call (zip ts args)
             ; return $ printf
               "    | %s%s => %s%s"
               (toName c)
               (sepStrings " " ("" : args))
               (toName c)
               (sepStrings " " ("" : calls))
             }
          where
            call (IndexArg,          z) = return z
            call (MvArg _,           z) = return z

            call (BindingArg _ _ nt, z) = call (NtArg nt, z)

            call (NtArg nt, z)
                | canBindIn aaa nt2 nt =
                    do { fn <- substName aaa nt mv2
                       ; return $ printf "(%s %s %s %s)" fn u x z
                       }
                | otherwise =
                    return z


{- ----------------------------------------------------------------------- -}
{- * Output for metavariables -}

{- | Generates text for metavariable declarations. -}

processMv :: ASTAnalysis -> MvRoot -> M String
processMv aa mv =
    do { mvd  <- getMvDecl aa mv
       ; name <- mvType aa mv
       ; return $ printf "Definition %s := (%s).\n\n" name (coqMvImplType mvd)
       }


{- ----------------------------------------------------------------------- -}
{- * Output for phantoms -}

{- | Generates text for phantom metavariable declarations. -}

processPhantom :: ASTAnalysis -> MvRoot -> M String
processPhantom aa mv =
    do { name <- mvType aa mv
       ; return $ printf "Parameter %s : Set.\n\n" name
       }


{- ----------------------------------------------------------------------- -}
{- * Output for \"fv\" -}

{- Generates the text for the @fv@ functions. -}

processFv :: ASTAnalysis -> [NtRoot] -> M String
processFv aa nts =
    do { s1 <- processFvDefs aa nts
       ; return $ s1
       }

{- Generates the text for the @fv@ functions. -}

processFvDefs :: ASTAnalysis -> [NtRoot] -> M String
processFvDefs aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ map join ss
       }
    where
      join strs = printf "Fixpoint %s.\n\n" (sepStrings "\n\nwith " strs)

      f aa nt1 nt2 mv2 =
          do { fv_fn           <- fvName aa nt1 mv2
             ; e               <- newName nt1
             ; etype           <- ntType aa nt1
             ; mvt             <- mvType aa mv2
             ; (Syntax _ _ cs) <- getSyntax aa nt1
             ; branches        <- mapM (local . branch nt1 nt2 mv2) cs
             ; return $ printf
               "%s (%s : %s) {struct %s} : %s %s :=\n\
               \  match %s with\n\
               \%s\n\
               \  end"
               fv_fn e etype e mvSetType mvt
               e
               (sepStrings "\n" branches)
             }

      branch nt1 nt2 mv2 c@(SConstr _ _ _ ts _) =
          do { args   <- mapM (newName . toRoot) ts
             ; calls' <- mapMM (call nt1 nt2 mv2) (zip ts args)
             ; let calls = if null calls' then [mvSetEmpty] else calls'
             ; return $ printf
               "    | %s%s => %s"
               (toName c)
               (sepStrings " " ("" : args))
               (sepStrings (" " ++ mvSetUnion ++ " ") calls)
             }

      call _   _   _   (IndexArg, _)          = return Nothing
      call nt1 nt2 mv2 (BindingArg _ _ nt, x) = call nt1 nt2 mv2 (NtArg nt, x)

      call _ _ mv2 (MvArg mv', x)
          | canonRoot aaa mv2 == canonRoot aaa mv' =
              return $ Just $ printf "(%s %s)" mvSetSingleton x
          | otherwise =
              return Nothing

      call _ nt2 mv2 (NtArg nt, x)
          | canBindIn aaa nt2 nt =
              do { fn <- fvName aaa nt mv2
                 ; return $ Just $ printf "(%s %s)" fn x
                 }
          | otherwise =
              return Nothing


{- ----------------------------------------------------------------------- -}
{- * Output for \"open\" -}

{- | Generates the text for the @open@ and @open_rec@ functions. -}

processOpen :: ASTAnalysis -> [NtRoot] -> M String
processOpen aa nts =
    do { s1 <- processOpenRecs aa nts
       ; s2 <- processOpenDefs aa nts
       ; return $ s1 ++ s2
       }

{- | Generates the text for the definitions of @open@. -}

processOpenDefs :: ASTAnalysis -> [NtRoot] -> M String
processOpenDefs aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ concat $ ss
       }
    where
      f aa nt1 nt2 mv2 =
          do { fn    <- openName aa nt1 mv2
             ; fnrec <- openRecName aa nt1 mv2
             ; e     <- newName nt1
             ; u     <- newName nt2
             ; return $ printf
               "Definition %s %s %s := %s 0 %s %s.\n\n"
               fn u e fnrec u e
             }

{- | Generates the text for the definitions of @open_rec@. -}

processOpenRecs :: ASTAnalysis -> [NtRoot] -> M String
processOpenRecs aaa nt1s =
    do { ss <- processNt1Nt2Mv2 aaa nt1s f
       ; return $ concat $ map join ss
       }
    where
      join strs = printf "Fixpoint %s.\n\n" (sepStrings "\n\nwith " strs)

      f aa nt1 nt2 mv2 =
          do { open_fn         <- openRecName aa nt1 mv2
             ; k               <- newName bvarRoot
             ; u               <- newName nt2
             ; utype           <- ntType aa nt2
             ; e               <- newName nt1
             ; etype           <- ntType aa nt1
             ; (Syntax _ _ cs) <- getSyntax aa nt1
             ; branches        <- mapM (local . branch nt1 nt2 mv2 k u) cs
             ; return $ printf
               "%s (%s : %s) (%s : %s) (%s : %s) {struct %s} : %s :=\n\
               \  match %s with\n\
               \%s\n\
               \  end"
               open_fn k bvarType u utype e etype e etype
               e
               (sepStrings "\n" branches)
             }

      branch nt1 nt2 mv2 k u c@(SConstr _ _ _ _ (Bound mv'))
          | canonRoot aaa nt1 == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
                do { n <- newName bvarRoot
                   ; return $ printf
                     "    | %s %s =>\n\
                     \      match %s %s %s with\n\
                     \        | inleft (left _)  => %s %s\n\
                     \        | inleft (right _) => %s\n\
                     \        | inright _        => %s (%s - 1)\n\
                     \      end"
                     (toName c) n
                     bvarLtEqLtDec n k
                     (toName c) n
                     u
                     (toName c) n
                   }
      branch nt1 nt2 mv2 k u c@(SConstr _ _ _ ts _) =
          do { args  <- mapM (newName . toRoot) ts
             ; calls <- mapM (call k u nt1 nt2 mv2) (zip ts args)
             ; return $ printf
               "    | %s%s => %s%s"
               (toName c)
               (sepStrings " " ("" : args))
               (toName c)
               (sepStrings " " ("" : calls))
             }

      call _ _ _ _ _ (IndexArg, x) = return x
      call _ _ _ _ _ (MvArg _,  x) = return x

      call k u _ nt2 mv2 (NtArg nt, x)
          | canBindIn aaa nt2 nt =
              do { fn <- openRecName aaa nt mv2
                 ; return $ printf "(%s %s %s %s)" fn k u x
                 }
          | otherwise =
              return x

      call k u nt1 nt2 mv2 (BindingArg mv' ntm nt, x)
          | canonRoot aaa ntm == canonRoot aaa nt2 &&
            canonRoot aaa mv2 == canonRoot aaa mv' =
                do { fn <- openRecName aaa nt mv2
                   ; let k' = "(S " ++ k ++ ")"
                   ; return $ printf "(%s %s %s %s)" fn k' u x
                   }
          | otherwise =
              call k u nt1 nt2 mv2 (NtArg nt, x)
