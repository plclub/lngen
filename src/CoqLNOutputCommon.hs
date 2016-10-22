{- | Implementation note (BEA): For the sake of consistency, some
   functions return a result in a monad, even when the functions are
   completely pure. -}

module CoqLNOutputCommon where

import Data.Map as Map

import AST
import ASTAnalysis
import MyLibrary ( sepStrings )


{- ----------------------------------------------------------------------- -}
{- * Constants: General -}

{- | Separator to use between parts of the generated output. -}

coqSep :: String
coqSep = "(* *********************************************************************** *)\n"

{- | The \"core\" hint database for Coq. -}

coreDb :: String
coreDb = "core"

{- | The hint database for \"brute force\" automation. -}

bruteDb :: String
bruteDb = "brute_force"

{- | The hint database for @lngen@ specific \"brute force\" automation
   via @auto@. -}

hintDb :: String
hintDb = "lngen"

{- | The name of the functional extensionality axiom. -}

funExtEq :: String
funExtEq = "@functional_extensionality_dep"

{- | The name of the well-founded induction on natural numbers
   for @Prop@. -}

ltWfInd :: String
ltWfInd = "lt_wf"

{- | The name of the well-founded induction on natural numbers
   for @Set@. -}

ltWfRec :: String
ltWfRec = "lt_wf_rec"


{- ----------------------------------------------------------------------- -}
{- * Constants: Related to decidable equality -}

{- | The infix operator for decidable equality. -}

decEq :: String
decEq = "=="


{- ----------------------------------------------------------------------- -}
{- * Constants: Related to finite sets -}

{- | The empty metavariable set. -}

mvSetEmpty :: String
mvSetEmpty = "empty"

{- | The type of finite sets of atoms. -}

mvSetType :: String
mvSetType = "atoms"

{- | The (infix) \"not in\" predicate on metavariable sets. -}

mvSetNotin :: String
mvSetNotin = "`notin`"

{- | The (prefix) remove operation on metavariable sets. -}

mvSetRemove :: String
mvSetRemove = "remove"

{- | The (prefix) singleton metavariable set constructor. -}

mvSetSingleton :: String
mvSetSingleton = "singleton"

{- | The (infix) union operation on metavariable sets. -}

mvSetUnion :: String
mvSetUnion = "`union`"


{- ----------------------------------------------------------------------- -}
{- * Constants: Related to indices -}

{- | The type of bound variables (indices). -}

bvarType :: String
bvarType = "nat"

{- | The root to use for bound variables (indices). -}

bvarRoot :: String
bvarRoot = "n"

{- | The name of the \"less-than\" predicate on bound variables. -}

bvarLt :: String
bvarLt = "lt"

{- | The name of the \"lt_eq_lt_dec\" predicate on bound variables. -}

bvarLtEqLtDec :: String
bvarLtEqLtDec = "lt_eq_lt_dec"

{- | The name of the \"lt_ge_dec\" predicate on bound variables. -}

bvarLtGeDec :: String
bvarLtGeDec = "lt_ge_dec"


{- ----------------------------------------------------------------------- -}
{- * Constructing names: Metavariables and nonterminals -}

{- | The type of atoms. -}

atomType :: Name
atomType = "atom"

{- | Returns the canonical short name for the given metavariable root. -}

mvRoot :: Monad m => ASTAnalysis -> MvRoot -> m Name
mvRoot aa mv = return $ canonRoot aa mv

{- | Returns the canonical short name for the given nonterminal root. -}

ntRoot :: Monad m => ASTAnalysis -> NtRoot -> m Name
ntRoot aa nt = return $ canonRoot aa nt

{- | Returns the canonical type for the given metavariable root. -}

mvType :: Monad m => ASTAnalysis -> MvRoot -> m Name
mvType aa mv = getMvDecl aa mv >>= \decl -> return (toName decl)

{- | Returns the canonical type for the given nonterminal root. -}

ntType :: Monad m => ASTAnalysis -> NtRoot -> m Name
ntType aa nt = getSyntax aa nt >>= \decl -> return (toName decl)


{- ----------------------------------------------------------------------- -}
{- * Constructing names: Functions -}

{- | Returns the name of the @close@ function, where the function is
   defined by induction on the first given nonterminal. -}

-- XXX BEA: I should use @mv2@ to generate the name, but the current
-- Ott backend doesn't properly handle the underlying case.

closeName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
closeName aa nt1 mv2 =
    do { n1 <- ntType aa nt1
       ; m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "close_" ++ n1 ++ "_wrt_" ++ m2
       }

{- | Returns the name of the @close_rec@ function, where the function
   is defined by induction on the first given nonterminal. -}

closeRecName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
closeRecName aa nt1 mv2 =
    closeName aa nt1 mv2 >>= \n -> return $ n ++ "_rec"

{- | Returns the name of the @fv@ function, where the function is
   defined by induction on the first given nonterminal. -}

fvName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
fvName aa nt1 mv2 =
    case Map.lookup (ntOfMv aa mv2, mv2) (fvMap aa) of
      Just n -> do { suffix <- ntType aa nt1
                   ; return $ n ++ "_" ++ suffix
                   }
      Nothing -> fail $ "No 'freevars' declaration for: " ++ (ntOfMv aa mv2) ++ " " ++ mv2 ++ "."

{- | Returns the name of the @open@ function, where the function is
   defined by induction on the first given nonterminal. -}

-- XXX BEA: I should use @mv2@ to generate the name, but the current
-- Ott backend doesn't properly handle the underlying case.

openName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
openName aa nt1 mv2 =
    do { n1 <- ntType aa nt1
       ; m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "open_" ++ n1 ++ "_wrt_" ++ m2
       }

{- | Returns the name of the @open_rec@ function, where the function
   is defined by induction the first given nonterminal. -}

openRecName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
openRecName aa nt1 mv2 =
    openName aa nt1 mv2 >>= \n -> return $ n ++ "_rec"

{- | Returns the name of the @size@ function. -}

sizeName :: Monad m => ASTAnalysis -> NtRoot -> m Name
sizeName aa nt = ntType aa nt >>= \n -> return $ "size_" ++ n

{- | Returns the name of the @subst@ function, where the function is
   defined by induction on the second given nonterminal. -}

substName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
substName aa nt1 mv2 =
    case Map.lookup (ntOfMv aa mv2, mv2) (substMap aa) of
      Just n -> do { suffix <- ntType aa nt1
                   ; return $ n ++ "_" ++ suffix
                   }
      Nothing -> fail $ "No 'substitutions' declaration for: " ++ (ntOfMv aa mv2) ++ " " ++ mv2 ++ "."


{- ----------------------------------------------------------------------- -}
{- * Constructing names: Induction principles -}

{- | Takes a list of names of types and returns the name to use with a
   @Combined Scheme@ declarations for @Prop@. -}

mutIndName :: [Name] -> Name
mutIndName []  = error "mutIndName: Internal error."
mutIndName ns  = sepStrings "_" ns ++ "_mutind"

{- | Takes the name of a type and returns the name to use with a
   @Scheme@ declaration for @Prop@. -}

schemeIndName :: Name -> Name
schemeIndName = (++ "_ind'")

{- | Takes a list of names of types and returns the name to use with a
   @Combined Scheme@ declarations for @Set@. -}

mutRecName :: [Name] -> Name
mutRecName []  = error "mutRecName: Internal error."
mutRecName ns  = sepStrings "_" ns ++ "_mutrec"

{- | Takes the name of a type and returns the name to use with a
   @Scheme@ declaration for @Set@. -}

schemeRecName :: Name -> Name
schemeRecName = (++ "_rec'")


{- ----------------------------------------------------------------------- -}
{- * Constructing names: Predicates -}

{- | Returns the name of the body predicate, where the main term is
   given by the first nonterminal. -}

bodyName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
bodyName aa nt1 mv2 =
    do { n1 <- ntType aa nt1
       ; m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "body_" ++ n1 ++ "_wrt_" ++ m2
       }

{- | Returns the name of the degree predicate, where the predicate is
   defined by induction on the first given nonterminal.  (For @Prop@.) -}

-- XXX BEA: I should use @mv2@ to generate the name, but the current
-- Ott backend doesn't properly handle the underlying case.

degreeName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
degreeName aa nt1 mv2 =
    do { n1 <- ntType aa nt1
       ; m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "degree_" ++ n1 ++ "_wrt_" ++ m2
       }

{- | Returns the name of the degree constructor, where the predicate
   is defined by induction on the first given nonterminal.  (For @Prop@.) -}

-- XXX BEA: I should use @mv2@ to generate the name, but the current
-- Ott backend doesn't properly handle the underlying case.

degreeConstrName :: Monad m => ASTAnalysis -> SConstr -> NtRoot -> MvRoot -> m Name
degreeConstrName aa sc _ mv2 =
    do { m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "degree_wrt_" ++ m2 ++ "_" ++ (toName sc)
       }

{- | Returns the name of the degree predicate, where the predicate is
   defined by induction on the first given nonterminal.  (For @Set@.) -}

-- XXX BEA: I should use @mv2@ to generate the name, but the current
-- Ott backend doesn't properly handle the underlying case.

degreeSetName :: Monad m => ASTAnalysis -> NtRoot -> MvRoot -> m Name
degreeSetName aa nt1 mv2 =
    do { n1 <- ntType aa nt1
       ; m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "degree_set_" ++ n1 ++ "_wrt_" ++ m2
       }

{- | Returns the name of the degree constructor, where the predicate
   is defined by induction on the first given nonterminal.  (For @Set@.) -}

-- XXX BEA: I should use @mv2@ to generate the name, but the current
-- Ott backend doesn't properly handle the underlying case.

degreeSetConstrName :: Monad m => ASTAnalysis -> SConstr -> NtRoot -> MvRoot -> m Name
degreeSetConstrName aa sc _ mv2 =
    do { m2 <- ntType aa (ntOfMv aa mv2)
       ; return $ "degree_set_wrt_" ++ m2 ++ "_" ++ (toName sc)
       }

{- | Returns the name of the local closure predicate for the given
   nonterminal.  (For @Prop@.) -}

lcName :: Monad m => ASTAnalysis -> NtRoot -> m Name
lcName aa nt = ntType aa nt >>= \n -> return $ "lc_" ++ n

{- | Returns the name of the local closure "universal" constructor for
   the given constructor, which is assumed to be for the given
   nonterminal.  (For @Prop@.) -}

lcConstrName :: Monad m => SConstr -> m Name
lcConstrName sc = return $ "lc_" ++ (toName sc)

{- | Returns the name of the local closure "exists" constructor for
   the given constructor, which is assumed to be for the given
   nonterminal.  (For @Prop@.) -}

lcExConstrName :: Monad m => SConstr -> m Name
lcExConstrName sc = lcConstrName sc >>= \n -> return $ n ++ "_ex"

{- | Returns the name of the local closure predicate for the given
   nonterminal.  (For @Set@.) -}

lcSetName :: Monad m => ASTAnalysis -> NtRoot -> m Name
lcSetName aa nt = getSyntax aa nt >>= \n -> return $ "lc_set_" ++ (toName n)

{- | Returns the name of the local closure "universal" constructor for
   the given constructor, which is assumed to be for the given
   nonterminal.  (For @Set@.) -}

lcSetConstrName :: Monad m => SConstr -> m Name
lcSetConstrName sc = return $ "lc_set_" ++ (toName sc)

{- | Returns the name of the local closure "exists" constructor for
   the given constructor, which is assumed to be for the given
   nonterminal.  (For @Set@.) -}

lcSetExConstrName :: Monad m => SConstr -> m Name
lcSetExConstrName sc = lcConstrName sc >>= \n -> return $ n ++ "_ex"


{- ----------------------------------------------------------------------- -}
{- * Constructing names: Swapping -}

{- | The name of the @swap@ function on @atom@s. -}

swapAtomName :: Name
swapAtomName = "swap_atom"

{- | Name of the \"swap" type class. -}

swapClass :: Name
swapClass = "Swap"

{- | The name of the \"swap_distrib\" type class field. -}

swapDistrib :: Name
swapDistrib = "swap_distrib"

{- | The name of the swapping function for the given nonterminal. -}

swapImplName :: Monad m => ASTAnalysis -> NtRoot -> m Name
swapImplName aa nt = ntType aa nt >>= \n -> return $ "swap_" ++ n

{- | The name of the \"swap_invol\" type class field. -}

swapInvol :: Name
swapInvol = "swap_invol"

{- | The name of the swapping function from the class definition. -}

swapName :: Name
swapName = "swap"

{- | The name of the \"swap_same\" type class field. -}

swapSame :: Name
swapSame = "swap_same"


{- ----------------------------------------------------------------------- -}
{- * Constructing names: Tactics -}

{- | The name of the tactic for applying a mutual induction principle. -}

applyMutInd :: String
applyMutInd = "apply_mutual_ind"

{- | The name of the default @auto@ tactic. -}

defaultAuto :: String
defaultAuto = "default_auto"

{- | The name of the default @autorewrite@ tactic. -}

defaultAutoRewr :: String
defaultAutoRewr = "default_autorewrite"

{- | The name of the default simplification tactic. -}

defaultSimp :: String
defaultSimp = "default_simp"

{- | The name of the default simplification tactic that doesn't do
   case analysis. -}

defaultSteps :: String
defaultSteps = "default_steps"

{- | The name of the tactic that decomposes hypotheses about set
   non-membership. -}

destructNotin :: String
destructNotin = "destruct_notin"

{- | The name of the tactic for using @eapply@ to apply the first
   applicable hypothesis. -}

eapplyFirst :: String
eapplyFirst = "eapply_first_hyp"

{- | The general purpose tactic for solving goals about finite sets. -}

fsetdecTac :: String
fsetdecTac = "fsetdec"

{- | The name of the tactic that \"gathers\" all atoms in the context. -}

gatherTac :: String
gatherTac = "gather_atoms"

{- | The name of the tactic that picks a fresh atom. -}

pickFreshTac :: String
pickFreshTac = "pick_fresh"

{- | The name of the tactic for renaming the last hypothesis. -}

renameLastTac :: String
renameLastTac = "rename_last_into"

{- | The name of the tactic for specializing all hypotheses. -}

specializeAllTac :: String
specializeAllTac = "specialize_all"

{- | The name of the tactic for proving the uniqueness of objects. -}

uniquenessTac :: String
uniquenessTac = "uniqueness"
