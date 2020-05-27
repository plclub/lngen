{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

{- | This module defines functions and data structures that allow one
   to analyze ASTs.  The results of such analysis might be useful for
   generating code for a proof assistant, for example.

   For each metavariable and nonterminal root, there is an associated
   \"canonical\" root.  However, multiple roots may denote the same
   metavariable or nonterminal.  It's conceptually cleaner to work in
   terms of only canonical roots, but this is less friendly to the
   user.  Generally, functions here will generally accept any root.

   We also define a representation for rules, 'Syntax', that captures
   the essential information needed to generate output for a theorem
   prover. -}

module ASTAnalysis (
    -- * Inductively defined syntax
    Syntax(..), SConstr(..), SConstrArg(..), MInfo(..),
    hasBindingArg,
    -- * AST analysis
    ASTAnalysis(..),
    MvMap, NtMap, SyntaxMap, NtGraph, MvSortList, SubordRelList,
    analyzeAST,
    -- * Queries
    getMvDecl,
    getSyntax,
    getBoundVarConstr,
    getFreeVarConstr,
    canBindIn,
    canBindOver,
    isOpenable,
    isSubordTo,
    mvsOfNt,
    ntOfMv,
    ) where

import Data.Generics       ( Data, Typeable, everything, mkQ )
import Data.Graph          ( graphFromEdges, reachable )
import Data.List           ( nub )
import Data.Map            ( Map )
import qualified Data.Map as Map
import Data.Maybe          ( fromJust, isJust, mapMaybe )
import Text.ParserCombinators.Parsec ( SourcePos )
import Control.Monad.Fail as Fail

import AST
import ComputationMonad
import MyLibrary ( getResult, mapLookup, nmap, shortestStr )


{- ----------------------------------------------------------------------- -}
{- * Inductively defined syntax -}

-- Implementation note (BEA): The 'Show' instances below are for
-- debugging purposes.  The default definitions are not really
-- suitable for general purpose printing.  Then again, there should be
-- no need, in general, to display these data structures.

{- | An inductively defined syntactic category, i.e., a nonterminal or
   rule, consists of a list of constructors.  The 'SourcePos' and
   'Name' fields should come from the corresponding 'Rule'. -}

data Syntax
    = Syntax SourcePos Name [SConstr]
    deriving ( Data, Show, Typeable )

instance Nameable Syntax where
    toName (Syntax _ n _) = n

instance SourceEntity Syntax where
    toPos (Syntax pos _ _) = pos

{- | A constructor consists of a short name (for use as a suffix), a
   long name (for use as the constructor's name), a list of types (one
   per argument), and a flag recording meta-information.  The
   'SourcePos's should come for the corresponding 'Production'. -}

data SConstr
    = SConstr SourcePos Name Name [SConstrArg] MInfo
    deriving ( Data, Show, Typeable )

instance Nameable SConstr where
    toName      (SConstr _ _ n _ _) = n

{- | Meta-information indicates whether a constructor is a free
   variable constructor (for some particular metavariable), bound
   variable constructor (for some particular metavariable), or neither
   of those. -}

data MInfo
    = Free MvRoot
    | Bound MvRoot
    | Normal
    deriving ( Data, Show, Typeable )

{- | The type of a constructor argument is specified indirectly, via
   the nonterminal or metavariable that was used in the original Ott
   input.  The important change here is that binders are represented
   using 'BindingArg', which is similar to 'BindDecl'. -}

data SConstrArg
    -- | A de Bruijn index.
    = IndexArg
    -- | A metavariable.
    | MvArg MvRoot
    -- | A nonterminal.
    | NtArg NtRoot
    -- | A nonterminal with a bound variable (the 'MvRoot').
    -- The first 'NtRoot' is the sort of the 'MvRoot'.
    | BindingArg MvRoot NtRoot NtRoot
    deriving ( Data, Show, Typeable )

instance Symbol SConstrArg where
    toRoot (IndexArg)         = "n"
    toRoot (MvArg r)          = r
    toRoot (NtArg r)          = r
    toRoot (BindingArg _ _ r) = r

{- | Converts a rule.  All constructors will be flagged as 'Normal'
   and have bogus metavariable sorts in 'BindingArg's. -}

toSyntax :: Rule -> Syntax
toSyntax r@(Rule pos _ prefix ps) =
    Syntax pos (toName r) (map toSConstr ps)
    where
      toSConstr (Production p es _ name bs) =
          SConstr p name (prefix ++ name) (mapMaybe toSConstrArg es) Normal

        where
          binders  = map (\(BindDecl _ mv' nt') -> (nt', mv')) bs
          getBound = toRoot . fromJust . flip lookup binders
          hasBound = isJust . flip lookup binders
          isBinder = isJust . flip lookup (map (\(a, b) -> (b, a)) binders)

          toSConstrArg (TElement _)
              = Nothing

          toSConstrArg (MvElement mv)
              | isBinder mv = Nothing
              | otherwise   = Just $ MvArg (toRoot mv)

          toSConstrArg (NtElement nt)
              | hasBound nt = Just $ BindingArg (getBound nt) "" (toRoot nt)
              | otherwise   = Just $ NtArg (toRoot nt)

{- | Takes a syntax definition produced by 'toSyntax' and fixes it to
   that it has correct free and bound variable constructors, and
   correct metavariable sorts on 'BindingArg's. -}

fixSyntax :: MvMap -> NtMap -> MvSortList -> Syntax -> Either ProgramError Syntax
fixSyntax mvm ntm mvsl (Syntax pos name cs) =
    do { cs' <- mapM toConstrs cs
       ; return $ Syntax pos name (concat cs')
       }
    where
      canon    = genCanonRoot mvm ntm
      sorts mv = nmap canon $ map snd $ filter ((==mv) . fst) mvsl

      toConstrs (SConstr p n n' [MvArg mv] minfo) =
          case sorts mv of
            [_] -> return [ SConstr p (n ++ "_f") (n' ++ "_f") [MvArg mv] (Free mv)
                          , SConstr p (n ++ "_b") (n' ++ "_b") [IndexArg] (Bound mv)
                          ]
            []  -> return [ SConstr p n n' [MvArg mv] minfo ]
            xs  -> abort  $ AmbiguousMvSort p mv xs

      toConstrs (SConstr p n n' args minfo) =
          do { args' <- mapM update args
             ; return [ SConstr pos n n' args' minfo ]
             }
          where
            update (BindingArg mv _ nt') =
                case sorts mv of
                  [nt] -> return $ BindingArg mv nt nt'
                  []   -> abort  $ NoMvSort p mv
                  xs   -> abort  $ AmbiguousMvSort p mv xs

            update x = return x

{- | Returns 'True' if and only if the given object has a 'BindingArg'
   somewhere in it. -}

hasBindingArg :: Data a => a -> Bool
hasBindingArg x = everything (||) (False `mkQ` isBindingArg) x
    where
      isBindingArg (BindingArg _ _ _) = True
      isBindingArg _                  = False


{- ----------------------------------------------------------------------- -}
{- * AST analysis -}

{- | Maps each metavariable root to its corresponding declaration. -}

type MvMap = Map MvRoot MetavarDecl

{- | Maps each nonterminal root to its corresponding declaration. -}

type NtMap = Map NtRoot Rule

{- | Maps each nonterminal root to its corresponding syntax definition. -}

type SyntaxMap = Map NtRoot Syntax

{- | A graph in the sense of the Data.Graph library, where each edge
   points from a nonterminal to a nonterminal that immediately depends
   on it.  The edges take into account the fact that there may be more
   than one root associated with each nonterminal.

   Implementation note: The first two components of each triple will
   always be the same.  This is an artifact of using Data.Graph in a
   setting where its full generality is not required. -}

type NtGraph = [(Root, Root, [Root])]

{- | A sort for a metavariable @mv@ is a nonterminal @nt@ such that
   @nt@ has a \"free variable constructor\" for @mv@, @mv@ appears as
   a binder in some nonterminal @nt'@ (where it binds in some @nt''@),
   and @nt@ is subordinate to @nt''@.  The map takes into account the
   fact that there may be more than one root associated with each
   nonterminal or metavariable. -}

type MvSortList = [(MvRoot, NtRoot)]

{- | The reflexive, transitive closure of the subordination relation,
   where @(s1, s2)@ means that @s1@ is subordinate to @s2@.  The
   relation includes all nonterminal roots and takes into account the
   fact that there may be more than one root associated with each
   nonterminal. -}

type SubordRelList = [(Root, Root)]

{- | Maps the @nt@-@mv@ pairs of a @freevars@ declaration to
     their names. -}

type FvMap = Map (MvRoot, NtRoot) Name

{- | Maps the @nt@-@mv@ pairs of a @substitutions@ declaration to
     their names. -}

type SubstMap = Map (MvRoot, NtRoot) Name

{- | Represents the results of analyzing an 'AST' as a record.  Each
   instance of this datatype corresponds to a particular 'AST', which
   can be viewed as an implicit argument to each field (function).  We
   define this datatype so that various facts about an 'AST' may be
   computed once and for all. -}

data ASTAnalysis = ASTAnalysis
    { mvMap :: MvMap
    -- ^ See the description of 'MvMap'.

    -- | See the description of 'NtMap'.
    , ntMap :: NtMap

    -- | See the description of 'SyntaxMap'.
    , syntaxMap :: SyntaxMap

    -- | See the description of 'FvMap'.
    , fvMap :: FvMap

    -- | See the description of 'SubstMap'.
    , substMap :: SubstMap

    -- | Returns the canonical root for the given root.
    , canonRoot :: Root -> Root

    -- | All canonical metavariable roots, not including \"phantoms.\"
    , mvRoots :: [MvRoot]

    -- | All canonical nonterminal roots.
    , ntRoots :: [NtRoot]

    -- | All canonical \"phantom\" metavariable roots.
    , phantomRoots :: [MvRoot]

    -- | See the description of 'NtGraph'.
    , ntGraph :: NtGraph

    -- | See the description of 'MvSortList'.
    , mvSorts :: MvSortList

    -- | See the description of 'SubordRelList'.
    , subordRel :: SubordRelList
    }

{- | Constructs an 'ASTAnalysis' object from an 'AST'.  Note that the
   supplied 'AST' is not preprocessed in anyway. -}

analyzeAST :: AST -> ASTAnalysis
analyzeAST ast@(AST _ rs substitutions freevars) =
    let mvm     = genMvMap ast
        ntm     = genNtMap ast
        crt     = genCanonRoot mvm ntm
        ntrs    = nmap crt (Map.keys ntm)
        ntg     = genNtGraph ntm
        mvs     = genMvSorts mvm ntm sub
        sub     = genSubordRel ntg

        fvm     = genFvMap mvm ntm freevars
        subm    = genSubstMap mvm ntm substitutions

        decls   = Map.assocs mvm
        mvrs    = nmap crt $ map fst $ filter (not . isPhantomMvDecl . snd) decls
        phrs    = nmap crt $ map fst $ filter (isPhantomMvDecl . snd) decls

        smap    = Map.fromList (concatMap zipR rs)
        zipR    = \(r@(Rule _ ns _ _)) -> zip ns (repeat (mungeR r))
        mungeR  = getResult . fixSyntax mvm ntm mvs . toSyntax

        aa = ASTAnalysis
             { mvMap        = mvm
             , ntMap        = ntm
             , syntaxMap    = smap
             , fvMap        = fvm
             , substMap     = subm
             , canonRoot    = crt
             , mvRoots      = mvrs
             , ntRoots      = ntrs
             , phantomRoots = phrs
             , ntGraph      = ntg
             , mvSorts      = mvs
             , subordRel    = sub
             }
    in
      aa


{- ----------------------------------------------------------------------- -}
{- * Generalized AST analysis functions -}

{- | The result takes into account all of the metavariable
   declarations that are present in the input AST. -}

genMvMap :: AST -> MvMap
genMvMap (AST mvds _ _ _) = foldr add Map.empty mvds
    where
      add o@(MetavarDecl _ ns _) m = foldr (\n a -> Map.insert n o a) m ns

{- | The result takes into account all of the nonterminal declarations
   and productions that are present in the input AST. -}

genNtMap :: AST -> NtMap
genNtMap (AST _ rs _ _) = foldr add Map.empty rs
    where
      add o@(Rule _ ns _ _) m = foldr (\n a -> Map.insert n o a) m ns

{- | Generates a 'FvMap' that can be queried without putting roots
   into canonical form first. -}

genFvMap :: MvMap -> NtMap -> [FvFun] -> SubstMap
genFvMap mvm ntm = foldr add Map.empty
    where
      add (FvFun nt mv n) m =
          m `Map.union` Map.fromList (zip (pairs nt mv) (repeat n))

      pairs nt mv =
          let (MetavarDecl _ mvs _) = fromJust $ Map.lookup mv mvm
              (Rule _ nts _ _)      = fromJust $ Map.lookup nt ntm
          in
            [ (nt', mv') | mv' <- mvs, nt' <- nts ]

{- | Generates a 'SubstMap' that can be queried without putting roots
   into canonical form first. -}

genSubstMap :: MvMap -> NtMap -> [SubstFun] -> SubstMap
genSubstMap mvm ntm = foldr add Map.empty
    where
      add (SingleSubstFun nt mv n) m =
          m `Map.union` Map.fromList (zip (pairs nt mv) (repeat n))

      pairs nt mv =
          let (MetavarDecl _ mvs _) = fromJust $ Map.lookup mv mvm
              (Rule _ nts _ _)      = fromJust $ Map.lookup nt ntm
          in
            [ (nt', mv') | mv' <- mvs, nt' <- nts ]

{- | Returns the canonical root for the given root. -}

genCanonRoot :: MvMap -> NtMap -> Root -> Root
genCanonRoot mvm ntm rt = Map.findWithDefault rt rt canonMap
    where
      canonMap               = Map.map f mvm `Map.union` Map.map g ntm
      f (MetavarDecl _ ns _) = shortestStr ns
      g (Rule _ ns _ _)      = shortestStr ns

{- | The result takes into account all nonterminals and productions
   present in the input maps. -}

genNtGraph :: NtMap -> NtGraph
genNtGraph ntm = nmap buildEdge (Map.keys ntm)
    where
      -- Stage 2: Take the "singleton" edges computed by 'addR' and
      -- collapse them into an 'NtGraph'.

      buildEdge k = (k, k, nmap snd $ filter ((==k) . fst) rel)
      rel         = nub $ concat $ Map.elems $ Map.mapWithKey addR ntm

      -- Stage 1: Go through every rule and production and generate
      -- "singleton" edges.

      addR k (Rule _ _ _ ps)                 = concatMap (addP k) ps
      addP k (Production _ es _ _ _)         = concat $ mapMaybe (addE k) es
      addE k (NtElement (Nonterminal _ n _)) = Just $ zip (find n) (repeat k)
      addE _ _                               = Nothing

      -- Stage 0: Build a table for looking up all of the nonterminal
      -- roots "equivalent" to a given one.

      find  = fromJust . flip lookup assoc
      assoc = do { nt              <- Map.keys ntm
                 ; (Rule _ ns _ _) <- mapLookup nt ntm
                 ; return (nt, ns)
                 }

{- | A sort for a metavariable @mv@ is a nonterminal @nt@ such that
   @nt@ has a \"free variable constructor\" for @mv@, @mv@ appears as
   a binder in some nonterminal @nt'@ (where it binds in some @nt''@),
   and @nt@ is subordinate to @nt''@.  The map takes into account the
   fact that there may be more than one root associated with each
   nonterminal or metavariable. -}

genMvSorts :: MvMap -> NtMap -> SubordRelList -> MvSortList
genMvSorts mvm ntm srel = concatMap sorts mvrs
    where

      -- Implementation note (BEA): Follow the description of 'MvSortList'.
      -- The 'nub' below is to remove duplicates.

      sorts mv =
          nub $ do { nt  <- ntrs
                   ; nt' <- ntrs
                   ; let (Rule _ _ _ ps)  = fromJust $ Map.lookup nt  ntm
                   ; let (Rule _ _ _ ps') = fromJust $ Map.lookup nt' ntm

                   -- nt has a "free variable constructor" for mv
                   ; _ <- filter (`isFreeConstr` mv) ps

                   -- the bit about binding
                   ; (Production _ _ _ _ bs) <- ps'
                   ; _ <- filter (isGoodBinding mv nt) bs
                   ; return (mv, nt)
                   }

      -- Implementation note (BEA): Helper functions and definitions.

      canon  = genCanonRoot mvm ntm
      mvrs   = Map.keys mvm
      ntrs   = Map.keys ntm

      isFreeConstr (Production _ es _ _ _) mv =
          case filter notTerminal es of
            [MvElement (Metavariable _ m _)] -> canon m == canon mv
            _                                -> False

      notTerminal (TElement _) = False
      notTerminal _            = True

      isGoodBinding mv nt (BindDecl _ left right) =
          canon m == canon mv && (nt, nt'') `elem` srel
          where
            Metavariable _ m    _ = left
            Nonterminal  _ nt'' _ = right

{- | Computes the reflexive, transitive closure of the subordination
   relation from the given graph. -}

genSubordRel :: NtGraph -> SubordRelList
genSubordRel ntg = concatMap buildTuples vertices
    where
      (g, vmap, kmap) = graphFromEdges ntg
      vertices        = mapMaybe kmap $ map (\(_,x,_) -> x) ntg

      -- Implementation note (BEA): It seems that 'reachable' includes
      -- "in zero steps," hence the "reflexive" bit.

      toR         v = case vmap v of (_, x, _) -> x
      buildTuples v = zip (repeat (toR v)) (map toR $ reachable g v)


{- ----------------------------------------------------------------------- -}
{- * Queries -}

{- Implementation note (BEA): The code in this section is easy to
   read, but it may turn out to be too inefficient in practice, e.g.,
   on large inputs.  These are common queries whose answers we end up
   recomputing every time they are needed. -}

{- | The lookup @return@s the result in the monad or else @fail@s. -}

getMvDecl :: MonadFail m => ASTAnalysis -> MvRoot -> m MetavarDecl
getMvDecl aa = flip mapLookup (mvMap aa)

{- | The lookup @return@s the result in the monad or else @fail@s. -}

getSyntax :: MonadFail m => ASTAnalysis -> NtRoot -> m Syntax
getSyntax aa = flip mapLookup (syntaxMap aa)

{- | The lookup @return@s the result in the monad or else @fail@s. -}

getBoundVarConstr :: MonadFail m => ASTAnalysis -> NtRoot -> MvRoot -> m SConstr
getBoundVarConstr aa nt mv =
    do { (Syntax pos _ cs) <- getSyntax aa nt
       ; case filter isBvar cs of
              [c] -> return c
              _   -> Fail.fail $ show pos ++ ": Internal error (getBoundVarConstr)."
       }

    where
      isBvar (SConstr _ _ _ _ (Bound mv'))
          | canonRoot aa mv == canonRoot aa mv' = True
      isBvar _                                  = False

{- | The lookup @return@s the result in the monad or else @fail@s. -}

getFreeVarConstr :: MonadFail m => ASTAnalysis -> NtRoot -> MvRoot -> m SConstr
getFreeVarConstr aa nt mv =
    do { (Syntax pos _ cs) <- getSyntax aa nt
       ; case filter isFvar cs of
              [c] -> return c
              _   -> Fail.fail $ show pos ++ ": Internal error (getFreeVarConstr)."
       }

    where
      isFvar (SConstr _ _ _ _ (Free mv'))
          | canonRoot aa mv == canonRoot aa mv' = True
      isFvar _                                  = False

{- | Returns 'True' if and only if the first nonterminal @nt1@ is
   bindable in the second nonterminal @nt2@, i.e., if there is a
   metavariable whose sort is @nt1@ and @nt1@ is subordinate to
   @nt2@. -}

canBindIn :: ASTAnalysis -> NtRoot -> NtRoot -> Bool
canBindIn aa nt1 nt2 =
    not (null (filter ((==nt1) . snd) (mvSorts aa))) &&
    isSubordTo aa nt1 nt2

{- | Symmetric version of 'canBindIn'. -}

canBindOver :: ASTAnalysis -> NtRoot -> NtRoot -> Bool
canBindOver aa = flip $ canBindIn aa

{- | A nonterminal @nt@is \"openable\" if there is some nonterminal
   @nt'@ that is bindable in it. -}

isOpenable :: ASTAnalysis -> NtRoot -> Bool
isOpenable aa nt = not $ null $ filter (canBindOver aa nt) (ntRoots aa)

{- | Tests if the first root is (reflexively and transitively)
    subordinate to the second root. -}

isSubordTo :: ASTAnalysis -> NtRoot -> NtRoot -> Bool
isSubordTo aa nt1 nt2 = (nt1, nt2) `elem` subordRel aa

{- | Returns the canonical metavariables whose sort is the given
   nonterminal. -}

mvsOfNt :: ASTAnalysis -> NtRoot -> [MvRoot]
mvsOfNt aa nt = nmap fst $ filter ((==cnt) . snd) sorts
    where
      canon         = canonRoot aa
      sorts         = nub $ map pcanon (mvSorts aa)
      cnt           = canon nt
      pcanon (x, y) = (canon x, canon y)

{- | Returns the canonical sort of the given metavariable root. -}

ntOfMv :: ASTAnalysis -> MvRoot -> NtRoot
ntOfMv aa mv =
    head $ nmap (canonRoot aa) $ map snd $ filter ((mv==) . fst) (mvSorts aa)
