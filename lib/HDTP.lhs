HDTP Implementation
===================

> module HDTP where
> import Data.List ((\\))


Basic Definitions
-----------------

We define a signature for our multi-sorted language, consisting of a set of Sorts, a set of function symbols (with an associated arity function), and a set of predicate symbols (with an associated arity function). We consider constants to be nullary functions (arFun c :: [] -> Sort)

Next, we define our set of variables as a set of functions, where a standard first-order variable is just a nullary function

> type FunSymb = String
> newtype PredSymb = PS String deriving (Eq, Show)
> type VarSymb = String

Then, we define our terms, both first- and second-order

> -- newtype Term Sg [[s], [f], [p], af, ap] [v] = v | f [Term] deriving (Eq,Ord,Show)
> data TSymb = VS VarSymb | FS FunSymb deriving (Eq, Show)
> data Term = T TSymb [Term] deriving (Eq, Show) -- Find a way to restrict this to respect sorts
> data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving (Eq, Show)

> newtype Sort = S String deriving Eq
> symbAr :: TSymb -> ([Sort], Sort)
> symbAr (VS "F") = ([S "a"], S "b")
> symbAr (VS "F'") = ([S "a"], S "b")
> symbAr (VS "G") = ([S "a"], S "b")
> predAr :: PredSymb -> ([Sort])
> predAr = undefined


Anti-Unification
-------------------

Now we define subsitution as they did

> data Sub = SR Renaming | SF Fixation | SI Insertion | SP Permutation
> apply :: Sub -> Form -> Form
> apply (SR r) (FT predSymb ts) = applyRenaming r (FT predSymb ts)
> apply (SF f) (FT predSymb ts) = applyFixation f (FT predSymb ts)
> apply (SI i) (FT predSymb ts) = applyInsertion i (FT predSymb ts)
> apply (SP p) (FT predSymb ts) = applyPermutation p (FT predSymb ts)
> apply r (Not form) = Not (apply r form)
> apply r (Disj form form') = Disj (apply r form) (apply r form')
> apply r (Forall w form) = Forall w (apply r form) -- TODO should a renaming rename bound variables?

A general substitution, usually not allowed:

> type GenSub = [(VarSymb, Term)]

And then we define the so-called ``basic substitutions''


Renaming
--------

> newtype Renaming = R (VarSymb, VarSymb)

> -- Checks whether two variables have the same arity
> sameArity :: VarSymb -> VarSymb -> Bool
> sameArity v v' = (symbAr (VS v)) == (symbAr (VS v'))

> renaming :: VarSymb -> VarSymb -> Maybe Renaming
> renaming v v' | sameArity v v' = Just $ R (v, v')
>               | otherwise = Nothing

> renameInVar :: Renaming -> VarSymb -> VarSymb
> renameInVar (R (v, v')) w | w == v    = v'
>                           | otherwise = w

> applyRenaming r (FT p ts) = FT p (map (renameInTerm r) ts) where
>   renameInTerm :: Renaming -> Term -> Term
>   renameInTerm r (T (VS w) ts) = T (VS (renameInVar r w)) ts
>   renameInTerm r (T (FS f) ts) = T (FS f) (map (renameInTerm r) ts)


Fixation
--------

> newtype Fixation = F (VarSymb, FunSymb)

> applyFixation r (FT p ts) = FT p (map (fixInTerm r) ts) where
>   fixInTerm :: Fixation -> Term -> Term
>   fixInTerm (F (v, f)) (T (VS w) ts) | w == v = T (FS f) ts
>                                      | otherwise = T (VS w) ts
>   fixInTerm r (T (FS f) ts) = T (FS f) (map (fixInTerm r) ts)

% > fix :: Fixation
% > fix = F (VS "X", FS "FFF")


Argument Insertion
------------------

>                              -- F,       F',      G,       i
> newtype Insertion = AI (VarSymb, VarSymb, VarSymb, Int)

> replace :: [Term] -> Term -> Int -> [Term]
> replace = undefined

% > replace ts t idx = Data.Foldable.foldr (:) [] $ S.update idx t $ S.fromList ts

> isArgument :: Int -> Int -> Int -> Bool
> isArgument i k idx = idx `elem` [i..i+k-1]

> applyInsertion ai (FT p ts) = FT p (map (insertInTerm ai) ts) where
>   insertInTerm :: Insertion -> Term -> Term
>   insertInTerm ai@(AI (f, f', g, i)) (T (VS v) ts) | v == f = let
>     k = length $ fst $ symbAr $ VS g
>     arguments = [ t | (idx, t) <- zip [0..] ts, isArgument i k idx ]
>     nonArguments = ts \\ arguments
>     in head ts

% >     insertInTerm ai@(AI (f, f', g, i)) (T (VS v) ts) | v == f = T (VS f') [ t | (idx, t) <- zip [0..] (replace ts (T (VS g) [ t | (idx, t) <- zip [0..] ts, isArgument i (length $ fst $ symbAr $ VS g) idx ]) i), not (isArgument i (length $ fst $ symbAr $ VS g) idx)]
% >                                                      | otherwise = T (VS v) (map (insertInTerm ai) ts)

>   insertInTerm ai (T (FS f) ts) = T (FS f) (map (insertInTerm ai) ts)

> ins :: Insertion
> ins = AI ("F", "F'", "G", 1)

> someForm2 :: Form
> someForm2 = FT (PS "P") [T (VS "F") [ T (FS "a") [], T (FS "b") [], T (FS "c") [], T (FS "d") []]]

> ppp2 :: Form
> ppp2 = apply (SI ins) someForm2


Permutation
-----------

> newtype Permutation = P (VarSymb, Int -> Int)

> -- this function permutes a list (given twice as argument because of the recusion), given a function f from indices (Int) to indices (Int) 
> -- Here it must hold that f assigns only indices smaller than length of the list to such indices, no checking whether f is bijective is done
> permute :: [a] -> [a] -> (Int -> Int) -> [a]
> permute [] l f = []
> permute (x:xs) l f = l!!f (length l - (length xs + 1)) : permute xs l f

> applyPermutation p (FT pr ts) = FT pr (map (permInTerm p) ts) where
>   permInTerm :: Permutation -> Term -> Term
>   permInTerm (P (v, f)) (T (VS w) ts) = T (VS w) (permute ts ts f)
>   permInTerm r (T (FS f) ts) = T (FS f) (map (permInTerm r) ts)

> fun :: Int -> Int
> fun 0 = 1
> fun 1 = 2
> fun 2 = 0

> perm :: Permutation
> perm = P ("X", fun) 

> -- to test: this is basically a formula P(X(a,b,c)). a,b,c are constants (zero-ary functions)
> someForm :: Form
> someForm = FT (PS "P") [T (VS "X") [ T (FS "a") [], T (FS "b") [], T (FS "c") []]]

> -- Output: FT (PS "P") [T (VS "X") [T (FS "b") [],T (FS "c") [],T (FS "a") []]]
> ppp :: Form
> ppp = apply (SP perm) someForm


Generalization
--------------

Next, we define, for any two terms, a generalization

% > type Gen = (Term, (Sub), (Sub))
% > gnrlz :: Term -> Term -> Gen
% > gnrlz s t = (g)

Now we define, for any set of generalizations, an algorithm for deciding which is/are the least general generalization(s) (lgg)

> -- lgg :: Term -> Term -> Gen
> -- lgg s t g:gs

Now we check a list of lggs and measure their relative complexities

> type Comp = Int

% > cSimple :: Sub -> Comp
% > c s   | s `elem` renames = 0
% >       | s `elem` fixations = 1
% >       | s `elem` argInserts = 1
% >       | s `elem` permutations = 1

% > c :: Gen -> Comp
% > c (g, s, t) = cSimple(s) + cSimple(t)

Following the HDTP paper, we want to write a new function for the complexity of a generalization
that takes into account whether it includes substitutions which have been reused

% > cReused :: [Gen] -> [Comp]

% > prefGen :: [Gen] -> Gen -- We're gonna need to use a Monad here!
% > --prefGen g:gs = 

Alignments
----------

Now we move into knowledge representation for real!

First, Domains

> type Domain = [Form]

Next, alignments, which are

> type Align = [(Form, Form)]

% > align :: Domain -> Domain -> Align

Then, domain generalizations

% > type DomGen = [Gen]
% > domGen :: Align -> DomGen

Then, mappings are lists of the substitutions from each generalization 

% > type Mapping = ([Sub], [Sub])
% > mapping :: DomGen -> Mapping
% > mapping (t, s, s') : gens = (s,s') : mapping gens


Examples
--------

Sorts
-----

> r = S "real"
> o = S "object"
> t = S "time"


Constants
---------

> sun = T (FS "s") []
> planet = T (FS "p") []


Functions
---------

> mass = FS "m"
> force = FS "f"
> distance = FS "d"
> gravity = FS "g"
> centrifugal = FS "c"


Predicates
----------

> revolvesAround = PS "ra"

% > predAr (PS "ra") = ([])

> form = FT revolvesAround [sun, planet]

Note: when the user defines their signature, we will prevent them from defining a non-sensical arity function, 
like one which allows predicates which take arguments, etc.

% > lambda :: Term -> Term -> [Sub] -> (Term, [Sub])
% > lambda t t' theta | t == t' = (t, theta)
% > lambda (T t t:ts) (T u u:us) theta | t == u = loop 
% >   loop 
