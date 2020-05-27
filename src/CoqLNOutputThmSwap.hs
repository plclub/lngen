{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -freduction-depth=50 #-}

module CoqLNOutputThmSwap where

import Text.Printf ( printf )

import AST
import ASTAnalysis
import ComputationMonad
import CoqLNOutputCommon
import CoqLNOutputCombinators

swapThms :: ASTAnalysis -> [[NtRoot]] -> M String
swapThms aa nts =
    do { swap_distribs  <- mapM (swap_distrib aa) nts
       ; swap_instances <- mapM (swap_instance aa) nts
       ; swap_invols    <- mapM (swap_invol aa) nts
       ; swap_sames     <- mapM (swap_same aa) nts
       ; return $ "Strategy opaque [ " ++ swapAtomName ++ " ].\n\n" ++
                  concat swap_sames ++
                  concat swap_invols ++
                  concat swap_distribs ++
                  concat swap_instances ++
                  "Strategy transparent [ " ++ swapAtomName ++ " ].\n\n" ++ "\n"
       }

{- | @swap ab (swap (c, d)  e) = ...@. -}

swap_distrib :: ASTAnalysis -> [NtRoot] -> M String
swap_distrib aaa nt1s =
    do { thms  <- processNt1 aaa nt1s thm
       ; names <- processNt1 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = mutPfStart Prop types ++ defaultSimp ++ "."
       ; mutualLemmaText Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 =
          do { swap <- swapImplName aa nt1
             ; return $ swap ++ "_distrib"
             }
      thm :: ASTAnalysis -> NtRoot -> M String
      thm aa nt1 =
          do { ab   <- newName "ab"
             ; c    <- newName "c"
             ; d    <- newName "d"
             ; e    <- newName nt1
             ; swap <- swapImplName aa nt1 
             ; return $ printf
               "forall %s %s %s %s,\n\
               \  %s %s (%s (%s, %s) %s) =\n\
               \  %s (%s %s %s, %s %s %s) (%s %s %s)"
               e ab c d
               swap ab swap c d e
               swap swapAtomName ab c swapAtomName ab d swap ab e
             }

{- | Theorem: @Swap@ instance declaration. -}

swap_instance :: ASTAnalysis -> [NtRoot] -> M String
swap_instance aa nts =
    do { defs <- mapM (local . def) nts
       ; return $ concat defs
       }
    where
      def nt =
          do { t    <- ntType aa nt
             ; swap <- swapImplName aa nt
             ; return $ printf
               "Instance %s_%s : %s %s := {\n\
               \  %s := %s\n\
               \}.\n\
               \Proof.\n\
               \  auto with %s.\n\
               \  auto with %s.\n\
               \  auto with %s.\n\
               \Defined.\n\
               \\n"
               swapClass t swapClass t
               swapName    swap
               hintDb
               hintDb
               hintDb
             }

{- | @swap ab (swap ab e) = e@. -}

swap_invol :: ASTAnalysis -> [NtRoot] -> M String
swap_invol aaa nt1s =
    do { thms  <- processNt1 aaa nt1s thm
       ; names <- processNt1 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = mutPfStart Prop types ++ defaultSimp ++ "."
       ; mutualLemmaText Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 =
          do { swap <- swapImplName aa nt1
             ; return $ swap ++ "_invol"
             }

      thm aa nt1 =
          do { ab   <- newName "ab"
             ; e    <- newName nt1
             ; swap <- swapImplName aa nt1
             ; return $ printf
               "forall %s %s,\n\
               \  %s %s (%s %s %s) = %s"
               e ab
               swap ab swap ab e e
             }

{- | @swap (a, a) e = e@. -}

swap_same :: ASTAnalysis -> [NtRoot]  -> M String
swap_same aaa nt1s =
    do { thms  <- processNt1 aaa nt1s thm
       ; names <- processNt1 aaa nt1s name
       ; types <- processNt1 aaa nt1s ntType
       ; let proof = mutPfStart Prop types ++ defaultSimp ++ "."
       ; mutualLemmaText Resolve NoRewrite NoHide [hintDb] Prop names thms proof
       }
    where
      name aa nt1 =
          do { swap <- swapImplName aa nt1
             ; return $ swap ++ "_same"
             }
      thm :: ASTAnalysis -> NtRoot -> M String
      thm aa nt1 =
          do { a    <- newName "a"
             ; e    <- newName nt1
             ; swap <- swapImplName aa nt1
             ; return $ printf
               "forall %s %s,\n\
               \  %s (%s, %s) %s = %s"
               e a
               swap a a e e
             }
