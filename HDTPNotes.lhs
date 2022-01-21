Title: HDTP Implementation



We define a signature for our multi-sorted language, consisting of a set of Sorts, 
a set of function symbols (with an associated arity function), and a set
of predicate symbols (with an associated arity function). We consider constants
to be nullary functions (arFun c :: [] -> Sort)

> type Sort = Int
> type FunSymb = String 
> type FunSg = ([Sort], Sort)
> type ArFun = FunSymb -> FunSg
> type PredSymb  = String
> type PredSg = [Sort]
> type ArPred = PredSymb -> PredSg 
>
> type Signature = ([Sort], [FunSymb], [PredSymb], ArFun, ArPred)

Next, we define our set of variables as a set of functions, where a standard first-order variable is just a nullary function

> type Var = ([Sort], Sort)

Then, we define our terms, both first- and second-order


> -- newtype Term Sg [[s], [f], [p], af, ap] [v] = v | f [Term] deriving (Eq,Ord,Show)
> data Term = Var | FunSymb [Term] -- Find a way to restrict this to respect sorts
> data Form = PredSymb [Term] | Not Form | Disj Form Form | Exists x Form | Forall x Form deriving (Eq,Ord,Show)
> 
> 
>

--------------------
3. Anti-Unification

Now we define subsitution as they did

> type Sub = [Var] -> Term
> sub xs 
> apply = map

And then we define the so-called ``basic substitutions''


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