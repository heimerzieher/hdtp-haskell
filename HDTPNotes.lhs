Title: HDTP Implementation



We define a signature for our multi-sorted language, consisting of a set of Sorts, 
a set of function symbols (with an associated arity function), and a set
of predicate symbols (with an associated arity function). We consider constants
to be nullary functions (arFun c :: [] -> Sort)

> newtype Sort = S String deriving Eq
> type FunSymb = String
> type FunSg = ([Sort], Sort)
> type ArFun = FunSymb -> FunSg
> newtype PredSymb = PS String deriving Show
> type PredSg = [Sort]
> type ArPred = PredSymb -> PredSg
>
> type Signature = ([Sort], [FunSymb], [PredSymb], ArFun, ArPred)

Next, we define our set of variables as a set of functions, where a standard first-order variable is just a nullary function

> type VarSymb = String
> type VarSg = ([Sort], Sort)

Then, we define our terms, both first- and second-order


> -- newtype Term Sg [[s], [f], [p], af, ap] [v] = v | f [Term] deriving (Eq,Ord,Show)
> data Symb = VS VarSymb | FS FunSymb deriving Show
> data Term = T Symb [Term] deriving Show -- Find a way to restrict this to respect sorts
> data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving Show

> symbAr :: Symb -> ([Sort], Sort)
> symbAr = undefined
> predAr :: PredSymb -> ([Sort])
> predAr = undefined

--------------------
3. Anti-Unification

Now we define subsitution as they did

> class Sub a where
>   apply :: a -> Form -> Form

A general substitution, usually not allowed:

> type GenSub = [(VarSymb, Term)]

And then we define the so-called ``basic substitutions''

> newtype Renaming = R (VarSymb, VarSymb)

> -- Checks whether two variables have the same arity
> sameArity :: 
> sameArity v v' = (symbAr (VS v)) == (symbAr (VS v'))

> renaming :: VarSymb -> VarSymb -> Maybe Renaming
> renaming v v' | sameArity v v' = Just $ R (v, v')
>               | otherwise = Nothing

> renameInVar :: Renaming -> VarSymb -> VarSymb
> renameInVar (R (v, v')) w | w == v    = v'
>                           | otherwise = w

> instance Sub Renaming where
>   apply r (FT p ts) = FT p (map (renameInTerm r) ts) where
>     renameInTerm :: Renaming -> Term -> Term
>     renameInTerm r (T (VS w) ts) = T (VS (renameInVar r w)) ts
>     renameInTerm r (T (FS f) ts) = T (FS f) (map (renameInTerm r) ts)
>     -- Purely recursive cases
>   apply r (Not f) = Not (apply r f)
>   apply r (Disj f f') = Disj (apply r f) (apply r f')
>   apply r (Forall w f) = Forall (renameInVar r w) (apply r f) -- TODO should a renaming rename bound variables?



% > f = Disj (Not (FT (PS "idk") $ [VS $ VS "X"])) (FT (PS "idk") $ [VS $ VS "Y"])
% > s = R (VS "X", VS "Y")
% > g = s `apply` f

Disj (Not (FT (PS "idk") [VS (VS "Y")])) (FT (PS "idk") [VS (VS "Y")])


> -- A renaming
> -- A fixation
> -- An argument insertion
> -- A permutation

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


------------------------
4. Alignments
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



> newtype Fixation = F (VarSymb, FunSymb)


X(Y)

> instance Sub Fixation where
>   apply r (FT p ts) = FT p (map (fixInTerm r) ts) where
>     fixInTerm :: Fixation -> Term -> Term
>     fixInTerm (F (v, f)) (T (VS w) ts) | w == v = T (FS f) ts
>                                        | otherwise = T (VS w) ts
>     fixInTerm r (T (FS f) ts) = T (FS f) (map (fixInTerm r) ts)
>   -- Purely recursive cases
>   apply r (Not f) = Not (apply r f)
>   apply r (Disj f f') = Disj (apply r f) (apply r f')
>   apply r (Forall w f) = Forall w (apply r f) -- TODO should a renaming rename bound variables?


% > fix :: Fixation
% > fix = F (VS "X", FS "FFF")


---- PERMUTATIONS ----




> newtype Permutation = P (VarSymb, Int -> Int)

> -- this function permutes a list (given twice as argument because of the recusion), given a function f from indices (Int) to indices (Int) 
> -- Here it must hold that f assigns only indices smaller than length of the list to such indices, no checking whether f is bijective is done
> permute :: [a] -> [a] -> (Int -> Int) -> [a]
> permute [] l f = []
> permute (x:xs) l f = l!!f (length l - (length xs + 1)) : permute xs l f


> instance Sub Permutation where
>   apply p (FT pr ts) = FT pr (map (permInTerm p) ts) where
>     permInTerm :: Permutation -> Term -> Term
>     permInTerm (P (v, f)) (T (VS w) ts) = T (VS w) (permute ts ts f)
>     permInTerm r (T (FS f) ts) = T (FS f) (map (permInTerm r) ts)
>   -- Purely recursive cases
>   apply p (Not f) = Not (apply p f)
>   apply p (Disj f f') = Disj (apply p f) (apply p f')
>   apply p (Forall w f) = Forall w (apply p f) -- TODO should a renaming rename bound variables?


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
> ppp = apply perm someForm


----------

---- Examples ---


----- Sorts ----

> r = S "real"
> o = S "object"
> t = S "time"

----- Constants ----

> sun = T (FS "s") []
> planet = T (FS "p") []

----- Functions ---

> mass = FS "m"
> force = FS "f"
> distance = FS "d"
> gravity = FS "g"
> centrifugal = FS "c"

----- Predicates ---

> revolvesAround = PS "ra"

% > predAr (PS "ra") = ([])

> form = FT revolvesAround [sun, planet]


Note: when the user defines their signature, we will prevent them from defining a non-sensical arity function, 
like one which allows predicates which take arguments, etc.

