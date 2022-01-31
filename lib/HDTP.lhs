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
> symbAr (VS "W") = ([S "a"], S "b")
> symbAr _ = undefined
> predAr :: PredSymb -> [Sort]
> predAr = undefined


Anti-Unification
-------------------

Now we define subsitution as they did

> data Sub = SR Renaming | SF Fixation | SI Insertion | SP Permutation deriving (Eq, Show)

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

> newtype Renaming = R (VarSymb, VarSymb) deriving (Eq, Show)

> -- Checks whether two variables have the same arity
> sameArity :: VarSymb -> VarSymb -> Bool
> sameArity v v' = symbAr (VS v) == symbAr (VS v')

> renaming :: VarSymb -> VarSymb -> Maybe Renaming
> renaming v v' | sameArity v v' = Just $ R (v, v')
>               | otherwise = Nothing

> renameInVar :: Renaming -> VarSymb -> VarSymb
> renameInVar (R (v, v')) w | w == v    = v'
>                           | otherwise = w

> applyRenaming :: Renaming -> Form -> Form
> applyRenaming r (FT p ts) = FT p (map renameInTerm ts) where
>   renameInTerm :: Term -> Term
>   renameInTerm (T (VS w) ts') = T (VS (renameInVar r w)) ts'
>   renameInTerm (T (FS f) ts') = T (FS f) (map renameInTerm ts')
> applyRenaming _ _ = undefined -- Recursive cases handled by apply



Fixation
--------

> newtype Fixation = F (VarSymb, FunSymb) deriving (Eq, Show)

> applyFixation :: Fixation -> Form -> Form
> applyFixation (F (v, f)) (FT p ts) = FT p (map fixInTerm ts) where
>   fixInTerm :: Term -> Term
>   fixInTerm (T (VS w) ts') | w == v = T (FS f) ts'
>                            | otherwise = T (VS w) ts'
>   fixInTerm (T (FS f') ts') = T (FS f') (map fixInTerm ts')
> applyFixation _ _ = undefined -- Recursive cases handled by apply

% > fix :: Fixation
% > fix = F (VS "X", FS "FFF")


Argument Insertion
------------------

>                              -- F,       F',      G,       i
> newtype Insertion = AI (VarSymb, VarSymb, VarSymb, Int) deriving (Eq, Show)

> applyInsertion :: Insertion -> Form -> Form
> applyInsertion (AI (f, f', g, i)) (FT p ts) = FT p (map insertInTerm ts) where
>   insertInTerm :: Term -> Term
>   insertInTerm (T (VS v) ts') | v /= f = T (VS v) (map insertInTerm ts)
>                               | otherwise = let
>     k = length $ fst $ symbAr $ VS g -- Amount of arguments that g takes
>     arguments = [ t | (j, t) <- zip [0..] ts', i <= j, j <= i+k-1 ] -- Arguments of f that will become arguments of g
>     in T (VS f') [ if j == i then T (VS g) (map insertInTerm arguments) else insertInTerm t | (j, t) <- zip [0..] ts', j `notElem` [i+1..i+k-1] ]
>   insertInTerm (T (FS f') ts') = T (FS f') (map insertInTerm ts')
> applyInsertion _ _ = undefined -- Recursive cases handled by apply

> ins :: Insertion
> ins = AI ("F", "F'", "G", 1)

> someForm2 :: Form
> someForm2 = FT (PS "P") [T (VS "F") [ T (FS "a") [], T (FS "b") [], T (FS "c") [], T (FS "d") []]]

> ppp2 :: Form
> ppp2 = apply (SI ins) someForm2


Permutation
-----------

> instance Show (a -> b) where
>        show a = "function"

> instance Eq (a -> b) where
>        (==) _ _ = True


> newtype Permutation = P (VarSymb, Int -> Int) deriving (Eq, Show)

> -- this function permutes a list (given twice as argument because of the recusion), given a function f from indices (Int) to indices (Int) 
> -- Here it must hold that f assigns only indices smaller than length of the list to such indices, no checking whether f is bijective is done
> permute :: [a] -> [a] -> (Int -> Int) -> [a]
> permute [] l f = []
> permute (x:xs) l f = l!!f (length l - (length xs + 1)) : permute xs l f

> applyPermutation :: Permutation -> Form -> Form
> applyPermutation p (FT pr ts) = FT pr (map (permInTerm p) ts) where
>   permInTerm :: Permutation -> Term -> Term
>   permInTerm (P (v, f)) (T (VS w) ts) = T (VS w) (permute ts ts f)
>   permInTerm r (T (FS f) ts) = T (FS f) (map (permInTerm r) ts)
> applyPermutation _ _ = undefined -- Recursive cases handled by apply

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


> list1 = [T (VS "X") [],T (VS "T") [],T (VS "Y") []]
> list2 = [T (VS "A") [],T (VS "B") [],T (VS "C") []]
> term1 = T (FS "B") list1
> subs0 = [SR $ R ("X", "Z")]

>-- lgg :: Term -> Term -> [Sub] -> (Term, [Sub])
>-- lgg t t' [] = (t, [])
>-- lgg t t' theta = (t, theta)

> lggRec :: [Term] -> [Term] -> [Sub] -> [(Term, [Sub])]
> lggRec [] [] theta = []
> lggRec (u:us) (t:ts) theta = (lgg u t theta) : lggRec us ts (snd (lgg u t theta))

> lgg :: Term -> Term -> [Sub] -> (Term, [Sub])
> lgg (T s (t:ts)) (T s' (t':ts')) theta  | (T s (t:ts)) == (T s' (t':ts'))  = ((T s (t:ts)), theta) -- Boring case
>                                     | s == s' && length (t:ts) == length (t':ts') = (T s (map fst (lggRec ts ts' theta))  , snd (last(lggRec ts ts' theta ))) -- Same top constructor case
                                 


First attempt, not accounting for Argument insertion or Permutations:



[(x1, Theta1), (x2, theta2).... (xn, theta_n)]

lst $ snd 

map (\(x, y) -> x) (lggRec ts ts' theta)

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


