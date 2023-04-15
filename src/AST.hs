{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{- | This module defines the abstract syntax tree for an Ott input
   file.  Only the following parts of an Ott file are representable:

     * some homomorphisms,
     * metavariable declarations,
     * nonterminal declarations,
     * binding specifications of the form \"(+ bind mv in nt +)\".
-}

module AST where

import Data.Typeable ( Typeable )
import Data.Data     ( Data(..) )
import Data.Maybe    ( mapMaybe )
import Text.ParserCombinators.Parsec ( SourcePos )

import MyLibrary ( sepStrings )


{- ----------------------------------------------------------------------- -}
{- * Orphan instances -}

{- Implementation note (BEA): These instances are not provided by
   Parsec, so I define them here.  I'm not entirely sure that they
   work, but they're the best that I can come up with given that
   'SourcePos' is opaque. -}

deriving instance (Typeable SourcePos)

{-
instance Typeable SourcePos where
    typeOf _ = mkTyConApp (mkTyCon "Text.ParserCombinators.Parsec.SourcePos") []


instance Data SourcePos where
    gfoldl     _ z c = z c
    gunfold    _ _ _ = undefined
    toConstr   _     = undefined
    dataTypeOf _     = mkNoRepType "Text.ParserCombinators.Parsec.SourcePos"
-}

{- ----------------------------------------------------------------------- -}
{- * Names and symbols -}

{- | A name is a non-empty string. -}

type Name = String

{- | A root is a non-empty sequence of letters. -}

type Root = String

{- | A suffix is a sequence of digits and primes. -}

type Suffix = String

{- | An unknown symbol consists of a root and a suffix.  It may stand
   for a metavariable or a nonterminal. -}

data UnknownSym
    = UnknownSym SourcePos Root Suffix
    deriving ( Data, Typeable )

instance Eq UnknownSym where
    (UnknownSym _ r1 s1) == (UnknownSym _ r2 s2) = r1 == r2 && s1 == s2

instance Show UnknownSym where
    show (UnknownSym _ r s) = r ++ s

{- | A metavariable consists of a root and a suffix. -}

data Metavariable
    = Metavariable SourcePos MvRoot MvSuffix
    deriving ( Data, Typeable )
type MvRoot   = Root
type MvSuffix = Suffix

instance Eq Metavariable where
    (Metavariable _ r1 s1) == (Metavariable _ r2 s2) = r1 == r2 && s1 == s2

instance Show Metavariable where
    show (Metavariable _ r s) = r ++ s

{- | A nonterminal consists of a root and a suffix. -}

data Nonterminal
    = Nonterminal SourcePos NtRoot NtSuffix
    deriving ( Data, Typeable )
type NtRoot   = Root
type NtSuffix = Suffix

instance Eq Nonterminal where
    (Nonterminal _ r1 s1) == (Nonterminal _ r2 s2) = r1 == r2 && s1 == s2

instance Show Nonterminal where
    show (Nonterminal _ r s) = r ++ s


{- ----------------------------------------------------------------------- -}
{- * Homomorphisms -}

{- | A homomorphism used to annotate a metavariable declaration. -}

data MetavarHom
    = CoqMvImplHom String
    -- ^ Specifies the implementation type for Coq.
    | MvPhantom
    -- ^ Specifies that no implementation should be provided.
    deriving ( Eq, Show )

{- | A homomorphism used to annotate a rule declaration. -}
newtype RuleHom = RuleHom {
      ruleHomPhantom :: Bool
    }
    deriving ( Eq, Show, Data )

instance Semigroup RuleHom where
  RuleHom {ruleHomPhantom = p1} <> RuleHom {ruleHomPhantom = p2} =
    RuleHom {ruleHomPhantom = p1 || p2}

instance Monoid RuleHom where
  mempty = RuleHom {ruleHomPhantom = False}

{- ----------------------------------------------------------------------- -}
{- * Metavariable declarations -}

{- | A metavariable declaration consists of a non-empty list of
   metavariable roots, which are all taken to denote a particular sort
   of variable in the language being defined, and a list of
   homomorphisms.  The list of homomorphisms should include at least
   one instance of anything "essential," e.g., an implementation
   type. -}

data MetavarDecl
    = MetavarDecl SourcePos [MvRoot] [MetavarHom]
    deriving ( Show )


{- ----------------------------------------------------------------------- -}
{- * Rules -}

{- | A rule defines a syntactic category in the language being
   defined.  It consists of a list of names used to denote terms
   defined by it, a name to be used in generating proof assistant
   output (e.g., as a prefix to all the constructor names), and a list
   of productions.

   The type arguments specify the following (in order): the type for
   elements in each production, the type for metavariables, and the
   type for nonterminals. -}

data GenRule a b c
    = Rule SourcePos RuleHom [NtRoot] Name [GenProduction a b c]
    deriving ( Data, Show, Typeable )

{- | A production consists of a list of elements, a list of flags, a
   constructor name, and a list binding specifications.  The type
   arguments are the same as for 'GenRule'. -}

data GenProduction a b c
    = Production SourcePos [a] [Flag] Name [GenBindingSpec b c]
    deriving ( Data, Typeable )

instance Show a => Show (GenProduction a b c) where
    show (Production _ es _ _ _) = sepStrings " " (map show es)

{- | A flag indicates that production is not a \"real\" constructor
   for the corresponding nonterminal. -}

data Flag
    = MFlag   -- ^ Metaproduction, e.g., for parsing.
    | IFlag   -- ^ Meaning unknown.
    | SFlag   -- ^ Meaning unknown.
    deriving ( Data, Typeable )

{- | An element defines one symbol in a production. -}

data Element
    = MvElement Metavariable   -- ^ Metavariable.
    | NtElement Nonterminal    -- ^ Nonterminal.
    | TElement String          -- ^ Terminal.
    deriving ( Data, Eq, Typeable )

instance Show Element where
    show (MvElement mv) = show mv
    show (NtElement nt) = show nt
    show (TElement s)   = s

{- | An unknown element is one in which we cannot distinguish between
   a metavariable and a nonterminal. -}

data UnknownElement
    = Variable UnknownSym   -- ^ Metavariable or nonterminal.
    | Unknown String        -- ^ Terminal.
    deriving ( Data, Eq, Typeable )

instance Show UnknownElement where
    show (Variable v) = show v
    show (Unknown s)  = s

{- | A binding specification specifies how the elements in a
   production form binding occurrences of variables.  The first type
   argument specifies the type for metavariables, and the second type
   argument specifies the type for nonterminals. -}

data GenBindingSpec a b
    = BindDecl SourcePos a b -- ^ (+ bind mv in nt +)
    deriving ( Data, Typeable )

instance (Show a, Show b) => Show (GenBindingSpec a b) where
    show (BindDecl _ v1 v2) =
        "(+ bind " ++ show v1 ++ " in " ++ show v2 ++ " +)"


{- ----------------------------------------------------------------------- -}
{- * Function names -}

{- | Records the user-supplied name for a generated substitution
   function. -}

data SubstFun
    = SingleSubstFun NtRoot MvRoot Name

{- | Records the user-supplied name for a generated free variables
   function. -}

data FvFun
    = FvFun NtRoot MvRoot Name


{- ----------------------------------------------------------------------- -}
{- * Abstract syntax trees -}

{- | A 'PreAST' is one in which metavariables and nonterminals have not
   yet been disambiguated. -}

data PreAST         = PreAST [MetavarDecl] [PreRule] [SubstFun] [FvFun]
type PreRule        = GenRule UnknownElement UnknownSym UnknownSym
type PreProduction  = GenProduction UnknownElement UnknownSym UnknownSym
type PreBindingSpec = GenBindingSpec UnknownSym UnknownSym

{- | An 'AST' is one in which metavariables and nonterminals have been
   disambiguated. -}

data AST         = AST [MetavarDecl] [Rule] [SubstFun] [FvFun]
type Rule        = GenRule Element Metavariable Nonterminal
type Production  = GenProduction Element Metavariable Nonterminal
type BindingSpec = GenBindingSpec Metavariable Nonterminal


{- ----------------------------------------------------------------------- -}
{- * Type classes -}

{- | A nameable entity is any type for which we can extract a name,
   e.g., something usable as a proof assistant implementation type or
   constructor name. -}

class Nameable a where
    toName :: a -> Name

    -- | By default, the same as 'toName'.
    toShortName :: a -> Name
    toShortName = toName

instance Nameable MetavarDecl where
    toName (MetavarDecl _ mvrs _) = head mvrs

instance Nameable (GenRule a b c) where
    toName (Rule _ _ ntrs _ _) = head ntrs

{- | A source entity is any type for which we can extract position
   information. -}

class SourceEntity a where
    -- | Extracts the source position of a symbol.
    toPos  :: a -> SourcePos
    -- | Extracts the source position of a symbol.
    -- Defined as @'show' . 'toPos'@ by default.
    toPosS :: a -> String
    toPosS = show . toPos

instance SourceEntity UnknownSym where
    toPos (UnknownSym pos _ _) = pos

instance SourceEntity Metavariable where
    toPos (Metavariable pos _ _) = pos

instance SourceEntity Nonterminal where
    toPos (Nonterminal pos _ _) = pos

instance SourceEntity MetavarDecl where
    toPos (MetavarDecl pos _ _) = pos

instance SourceEntity (GenRule a b c) where
    toPos (Rule pos _ _ _ _) = pos

instance SourceEntity (GenProduction a b c) where
    toPos (Production pos _ _ _ _) = pos

instance SourceEntity (GenBindingSpec a b) where
    toPos (BindDecl pos _ _) = pos

{- | A symbol is any type for which we can extract a \"root\". -}

class Symbol a where
    -- | Extracts the root of a symbol.
    toRoot :: a -> Root

instance Symbol UnknownSym where
    toRoot (UnknownSym _ r _) = r

instance Symbol Metavariable where
    toRoot (Metavariable _ r _) = r

instance Symbol Nonterminal where
    toRoot (Nonterminal _ r _) = r


{- ----------------------------------------------------------------------- -}
{- * Simple AST constants and queries -}

{- | Returns the Coq implementation type for the given metavariable. -}

coqMvImplType :: MetavarDecl -> String
coqMvImplType (MetavarDecl _ _ homs) = head $ mapMaybe f homs
    where
      f (CoqMvImplHom s) = Just s
      f _                = Nothing

{- | 'True' if and only if the declaration is for a \"phantom\"
   metavariable. -}

isPhantomMvDecl :: MetavarDecl -> Bool
isPhantomMvDecl (MetavarDecl _ _ homs) = MvPhantom `elem` homs

{- | 'True' if and only if the rule is for a \"phantom\"
   AST. -}
isPhantomRule :: Rule -> Bool
isPhantomRule (Rule _ hom _ _ _) = ruleHomPhantom hom
