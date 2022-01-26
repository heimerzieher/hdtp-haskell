Title: HDTP Implementation



We define a signature for our multi-sorted language, consisting of a set of Sorts, 
a set of function symbols (with an associated arity function), and a set
of predicate symbols (with an associated arity function). We consider constants
to be nullary functions (arFun c :: [] -> Sort)

> newtype Sort = S String
> newtype FunSymb = FS String deriving Show
> type FunSg = ([Sort], Sort)
> type ArFun = FunSymb -> FunSg
> newtype PredSymb = PS String deriving Show
> type PredSg = [Sort]
> type ArPred = PredSymb -> PredSg
>
> type Signature = ([Sort], [FunSymb], [PredSymb], ArFun, ArPred)

Next, we define our set of variables as a set of functions, where a standard first-order variable is just a nullary function

> newtype VarSymb = VS String deriving (Show, Eq)
> type VarSg = ([Sort], Sort)

Then, we define our terms, both first- and second-order


> -- newtype Term Sg [[s], [f], [p], af, ap] [v] = v | f [Term] deriving (Eq,Ord,Show)
> data Term = TV VarSymb | TF FunSymb [Term] deriving (Show) -- Find a way to restrict this to respect sorts
> data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving Show


--------------------
3. Anti-Unification

Now we define subsitution as they did

> class Sub a where
>   apply :: a -> Form -> Form

A general substitution, usually not allowed:

> type GenSub = [(VarSymb, Term)]

And then we define the so-called ``basic substitutions''

> newtype Renaming = R (VarSymb, VarSymb)

> renameInVar :: Renaming -> VarSymb -> VarSymb
> renameInVar (R (v, v')) w | w == v    = v'
>                           | otherwise = w

> instance Sub Renaming where
>   apply r (FT p []) = FT p []
>   apply r (FT p (t:ts)) = FT p ((renameInTerm r t):(map (renameInTerm r) ts)) where
>     renameInTerm :: Renaming -> Term -> Term
>     renameInTerm r (TV w) = TV (renameInVar r w)
>     renameInTerm r (TF f []) = TF f []
>     renameInTerm r (TF f (t:ts)) = TF f ((renameInTerm r t):(map (renameInTerm r) ts))
> -- Purely recursive cases
>   apply r (Not f) = Not (apply r f)
>   apply r (Disj f f') = Disj (apply r f) (apply r f')
>   apply r (Forall w f) = Forall (renameInVar r w) (apply r f) -- TODO should a renaming rename bound variables?

Quick test:

> f = Disj (Not (FT (PS "idk") $ [TV $ VS "X"])) (FT (PS "idk") $ [TV $ VS "Y"])
> s = R (VS "X", VS "Y")
> s `apply` f

Disj (Not (FT (PS "idk") [TV (VS "Y")])) (FT (PS "idk") [TV (VS "Y")])


> -- A renaming
> -- A fixation
> -- An argument insertion
> -- A permutation

Next, we define, for any two terms, a generalization

> type Gen = (Term, (Sub), (Sub))
> gnrlz :: Term -> Term -> Gen
> gnrlz s t = (g)


Now we define, for any set of generalizations, an algorithm for deciding which is/are the least general generalization(s) (lgg)

> -- lgg :: Term -> Term -> Gen
> -- lgg s t g:gs

Now we check a list of lggs and measure their relative complexities

> type Comp = Int

> cSimple :: Sub -> Comp
> c s   | s `elem` renames = 0
>       | s `elem` fixations = 1
>       | s `elem` argInserts = 1
>       | s `elem` permutations = 1

> c :: Gen -> Comp
> c (g, s, t) = cSimple(s) + cSimple(t)

Following the HDTP paper, we want to write a new function for the complexity of a generalization
that takes into account whether it includes substitutions which have been reused

> cReused :: [Gen] -> [Comp]

> prefGen :: [Gen] -> Gen -- We're gonna need to use a Monad here!
> --prefGen g:gs = 


------------------------
4. Alignments
Now we move into knowledge representation for real!

First, Domains

> type Domain = [Form]


Next, alignments, which are

> type Align = [(Form, Form)]

> align :: Domain -> Domain -> Align

Then, domain generalizations

> type DomGen = [Gen]
> domGen :: Align -> DomGen

Then, mappings are lists of the substitutions from each generalization 

> type Mapping = ([Sub], [Sub])
> mapping :: DomGen -> Mapping
> mapping (t, s, s') : gens = (s,s') : mapping gens



> newtype Fixation = F (VarSymb, FunSymb)

> fixInFun :: Fixation -> Term -> Term
> fixInFun (F (v, f)) (TV w) | w == v = TF f [] 
                             | otherwise = TV w
> fixInFun (F (v, v')) (TF f x) = TF f x


 --data Term = TV VarSymb | TF FunSymb [Term] deriving (Show) -- Find a way to restrict this to respect sorts
 --data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving Show

> instance Sub Fixation where
>  apply r (FT p []) = FT p []
> apply r (FT p (t:ts)) = FT p (fixInTerm r t:map (fixInTerm r) ts) where
>    fixInTerm :: Fixation -> Term -> Term
>    fixInTerm r (TV w) = fixInFun r (TV w)
>    fixInTerm r (TF f []) = TF f []
>    fixInTerm r (TF f (t:ts)) = TF f (fixInTerm r t:map (fixInTerm r) ts)
> -- Purely recursive cases
>  apply r (Not f) = Not (apply r f)
>  apply r (Disj f f') = Disj (apply r f) (apply r f')
>  apply r (Forall w f) = Forall w (apply r f) -- TODO should a renaming rename bound variables?


> fix :: Fixation
> fix = F (VS "X", FS "FFF")
