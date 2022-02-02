

HDTP Implementation
===================

\begin{code}
 module HDTP where
 import Data.List ((\\), find)
\end{code}


Basic Definitions
-----------------

We define a signature for our multi-sorted language, consisting of a set of Sorts, a set of function symbols (with an associated arity function), and a set of predicate symbols (with an associated arity function). We consider constants to be nullary functions (arFun c :: [] -> Sort)

Next, we define our set of variables as a set of functions, where a standard first-order variable is just a nullary function

\begin{code}
 type FunSymb = String
 newtype PredSymb = PS String deriving (Eq, Show)
 type VarSymb = String
\end{code}

Then, we define our terms, both first- and second-order

\begin{code}
 -- newtype Term Sg [[s], [f], [p], af, ap] [v] = v | f [Term] deriving (Eq,Ord,Show)
 data TSymb = VS VarSymb | FS FunSymb deriving (Eq, Show)
 data Term = T TSymb [Term] deriving (Eq, Show) -- Find a way to restrict this to respect sorts
 data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving (Eq, Show)

 newtype Sort = S String deriving (Eq, Show)
 symbAr :: TSymb -> ([Sort], Sort)
 symbAr (VS "F") = ([S "a"], S "b")
 symbAr (VS "F'") = ([S "a"], S "b")
 symbAr (VS "G") = ([S "a"], S "b")
 symbAr (VS "W") = ([S "a"], S "b")
 symbAr _ = undefined
 predAr :: PredSymb -> [Sort]
 predAr = undefined

\end{code}

Anti-Unification
-------------------

Now we define subsitution as they did

\begin{code}
 data Sub = SR Renaming | SF Fixation | SI Insertion | SP Permutation deriving (Eq, Show)

 apply :: Sub -> Form -> Form
 apply (SR r) (FT predSymb ts) = applyRenaming r (FT predSymb ts)
 apply (SF f) (FT predSymb ts) = applyFixation f (FT predSymb ts)
 apply (SI i) (FT predSymb ts) = applyInsertion i (FT predSymb ts)
 apply (SP p) (FT predSymb ts) = applyPermutation p (FT predSymb ts)
 apply r (Not form) = Not (apply r form)
 apply r (Disj form form') = Disj (apply r form) (apply r form')
 apply r (Forall w form) = Forall w (apply r form) -- TODO should a renaming rename bound variables?
\end{code}

A general substitution, usually not allowed:

\begin{code}
 type GenSub = [(VarSymb, Term)]
\end{code}

And then we define the so-called ``basic substitutions''


Renaming
--------

\begin{code}
 newtype Renaming = R (VarSymb, VarSymb) deriving (Eq, Show)

 -- Checks whether two variables have the same arity
 sameArity :: VarSymb -> VarSymb -> Bool
 sameArity v v' = symbAr (VS v) == symbAr (VS v')

 renaming :: VarSymb -> VarSymb -> Maybe Renaming
 renaming v v' | sameArity v v' = Just $ R (v, v')
               | otherwise = Nothing

 renameInVar :: Renaming -> VarSymb -> VarSymb
 renameInVar (R (v, v')) w | w == v    = v'
                           | otherwise = w

 applyRenaming :: Renaming -> Form -> Form
 applyRenaming r (FT p ts) = FT p (map renameInTerm ts) where
   renameInTerm :: Term -> Term
   renameInTerm (T (VS w) ts') = T (VS (renameInVar r w)) ts'
   renameInTerm (T (FS f) ts') = T (FS f) (map renameInTerm ts')
 applyRenaming _ _ = undefined -- Recursive cases handled by apply

\end{code}

Fixation
--------

\begin{code}
 newtype Fixation = F (VarSymb, FunSymb) deriving (Eq, Show)

 applyFixation :: Fixation -> Form -> Form
 applyFixation (F (v, f)) (FT p ts) = FT p (map fixInTerm ts) where
   fixInTerm :: Term -> Term
   fixInTerm (T (VS w) ts') | w == v = T (FS f) ts'
                            | otherwise = T (VS w) ts'
   fixInTerm (T (FS f') ts') = T (FS f') (map fixInTerm ts')
 applyFixation _ _ = undefined -- Recursive cases handled by apply

-- fix :: Fixation
-- fix = F (VS "X", FS "FFF")
\end{code}

Argument Insertion
------------------

\begin{code}
                              -- F,       F',      G,       i
 newtype Insertion = AI (VarSymb, VarSymb, VarSymb, Int) deriving (Eq, Show)

 applyInsertion :: Insertion -> Form -> Form
 applyInsertion (AI (f, f', g, i)) (FT p ts) = FT p (map insertInTerm ts) where
   insertInTerm :: Term -> Term
   insertInTerm (T (VS v) ts') | v /= f = T (VS v) (map insertInTerm ts)
                               | otherwise = let
     k = length $ fst $ symbAr $ VS g -- Amount of arguments that g takes
     arguments = [ t | (j, t) <- zip [0..] ts', i <= j, j <= i+k-1 ] -- Arguments of f that will become arguments of g
     in T (VS f') [ if j == i then T (VS g) (map insertInTerm arguments) else insertInTerm t | (j, t) <- zip [0..] ts', j `notElem` [i+1..i+k-1] ]
   insertInTerm (T (FS f') ts') = T (FS f') (map insertInTerm ts')
 applyInsertion _ _ = undefined -- Recursive cases handled by apply

 ins :: Insertion
 ins = AI ("F", "F'", "G", 1)

 someForm2 :: Form
 someForm2 = FT (PS "P") [T (VS "F") [ T (FS "a") [], T (FS "b") [], T (FS "c") [], T (FS "d") []]]

 ppp2 :: Form
 ppp2 = apply (SI ins) someForm2
\end{code}

Permutation
-----------

\begin{code}
 instance Show (a -> b) where
        show a = "function"

 instance Eq (a -> b) where
        (==) _ _ = True


 newtype Permutation = P (VarSymb, VarSymb,Int -> Int) deriving (Eq, Show)

 -- this function permutes a list (given twice as argument because of the recusion), given a function f from indices (Int) to indices (Int) 
 -- Here it must hold that f assigns only indices smaller than length of the list to such indices, no checking whether f is bijective is done
 permute :: [a] -> [a] -> (Int -> Int) -> [a]
 permute [] l f = []
 permute (x:xs) l f = l!!f (length l - (length xs + 1)) : permute xs l f

 applyPermutation :: Permutation -> Form -> Form
 applyPermutation p (FT pr ts) = FT pr (map (permInTerm p) ts) where
   permInTerm :: Permutation -> Term -> Term
   permInTerm (P (v, v', f)) (T (VS w) ts) | v == w = T (VS v') (permute ts ts f) --- here something is weird
                                           | otherwise = T (VS w) ts
   permInTerm r (T (FS f) ts) = T (FS f) (map (permInTerm r) ts)
 applyPermutation _ _ = undefined -- Recursive cases handled by apply

 fun :: Int -> Int
 fun 0 = 1
 fun 1 = 2
 fun 2 = 0

 perm :: Permutation
 perm = P ("X", "Y", fun) 

 -- to test: this is basically a formula P(X(a,b,c)). a,b,c are constants (zero-ary functions)
 someForm :: Form
 someForm = FT (PS "P") [T (VS "X") [ T (FS "a") [], T (FS "b") [], T (FS "c") []]]

 -- Output: FT (PS "P") [T (VS "X") [T (FS "b") [],T (FS "c") [],T (FS "a") []]]
 ppp :: Form
 ppp = apply (SP perm) someForm
\end{code}

Generalization
--------------

Next, we define, for any two terms, a generalization

\begin{code}
-- type Gen = (Term, (Sub), (Sub))
-- gnrlz :: Term -> Term -> Gen
-- gnrlz s t = (g)
\end{code}

Now we define, for any set of generalizations, an algorithm for deciding which is/are the least general generalization(s) (lgg)


First attempt, not accounting for Argument insertion or Permutations:


\begin{code}
--[(x1, Theta1), (x2, theta2).... (xn, theta_n)]

--lst $ snd 

--map (\(x, y) -> x) (lggRec ts ts' theta)
\end{code}

Now we check a list of lggs and measure their relative complexities

\begin{code}
 --type Comp = Int

 --cSimple :: Sub -> Comp
 --c s   | s `elem` renames = 0
 --      | s `elem` fixations = 1
  --     | s `elem` argInserts = 1
  --     | s `elem` permutations = 1

 --c :: Gen -> Comp
 --c (g, s, t) = cSimple(s) + cSimple(t)
\end{code}

Following the HDTP paper, we want to write a new function for the complexity of a generalization
that takes into account whether it includes substitutions which have been reused

\begin{code}
-- cReused :: [Gen] -> [Comp]

-- prefGen :: [Gen] -> Gen -- We're gonna need to use a Monad here!
-- --prefGen g:gs = 
\end{code}

Alignments
----------

Now we move into knowledge representation for real!

First, Domains

\begin{code}
 type Domain = [Form]
\end{code}

Next, alignments, which are

\begin{code}
-- type Align = [(Form, Form)]

-- align :: Domain -> Domain -> Align
\end{code}

Then, domain generalizations

% > type DomGen = [Gen]
% > domGen :: Align -> DomGen

Then, mappings are lists of the substitutions from each generalization 

% > type Mapping = ([Sub], [Sub])
% > mapping :: DomGen -> Mapping
% > mapping (t, s, s') : gens = (s,s') : mapping gens



Generalization

> --------------



Next, we define, for any two terms, a generalization

\begin{code}
 type Gen = (Form, Sub, Sub)

-- gnrlz :: Term -> Term -> Gen
-- gnrlz s t = (g)

\end{code}

Now we define, for any set of generalizations, an algorithm for deciding which is/are the least general generalization(s) (lgg)

Takes two terms $f(t_1 ... t_n), f(u_1...u_n)$, and then applies $\lambda (t_1, u_1)$


$f( (g_1,s,t) , (g_2,s,t) ....  )$

The following is an implemenation of that 

\begin{code}

 list1 = [T (VS "X") [],T (VS "T") [],T (VS "Y") []]
 list2 = [T (VS "A") [],T (VS "B") [],T (VS "C") []]
 term1 = T (FS "B") list1
 subs0 = [SR $ R ("X", "Z")]



 lgg :: Term -> Term -> [Sub] -> (Term, [Sub])
 lgg (T s (t:ts)) (T s' (t':ts')) theta  | (T s (t:ts)) == (T s' (t':ts'))  = ((T s (t:ts)), theta) -- Boring case
                                         | s == s' && length (t:ts) == length (t':ts') = (T s (map fst termSubsList)  , snd (last(termSubsList))) where -- Same top constructor case with f(t1,..tn) f(u1,...un)
                                                    termSubsList = lggRec ts ts' theta  
                                                    lggRec :: [Term] -> [Term] -> [Sub] -> [(Term, [Sub])]
                                                    lggRec [] [] theta = []
                                                    lggRec (u:us) (t:ts) theta = (lgg u t theta) : lggRec us ts (snd (lgg u t theta))

                                         
\end{code}


\begin{code}

 -- TODO integrate this type with our preexisting stuff
 type Subs = (VarSymb, Term, Term)

 -- Produces a VarSymb NOT in the provided list.
 newVariable :: [VarSymb] -> VarSymb
 newVariable = undefined
-- (a -> Bool) -> [a] -> Maybe a
 lambdaForTerms :: Term -> Term -> [Subs] -> (Term, [Subs])
 lambdaForTerms t u theta | t == u = (t, theta)
 lambdaForTerms (T (FS f) ts) (T (FS f') us) theta | f == f' = (\(terms, y) -> (T (FS f) terms, y)) $ foldr (\(term, theta) (termAcc, thetaAcc) -> (term:termAcc, theta ++ thetaAcc)) ([], theta) (zipWith (\x y -> lambdaForTerms x y []) ts us)
 lambdaForTerms t u theta = case find (\(_, t', u') -> t == t' && u == u') theta of
   Just (x, _, _) -> (T (VS x) [], theta)
   Nothing -> (T (VS x) [], (x, t, u):theta) where x = newVariable (map (\(x, _, _) -> x) theta)

 lambda :: Form -> Form -> [Subs] -> (Form, [Subs])
 lambda phi psi theta | phi == psi = (phi, theta)
 lambda (FT ps ts) (FT ps' us) theta | ps == ps' = (\(terms, y) -> (FT ps terms, y)) $ foldr (\(term, theta) (termAcc, thetaAcc) -> (term:termAcc, theta ++ thetaAcc)) ([], theta) (zipWith (\x y -> lambdaForTerms x y []) ts us)
 lambda (Not phi) (Not psi) theta = (Not outForm, subs) where (outForm, subs) = lambda phi psi theta
 lambda (Disj phi phi') (Disj psi psi') theta = (Disj outForm outForm', subs ++ subs') where
   (outForm, subs) = lambda phi psi theta
   (outForm', subs') = lambda phi' psi' theta
 lambda (Forall vs form) (Forall vs' form') theta = undefined -- TODO
 lambda _ _ _ = undefined

\end{code}

\begin{code}
-- data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving (Eq, Show)
\end{code}

\begin{code}

--[(x1, Theta1), (x2, theta2).... (xn, theta_n)]
-- $, [Sub])
-- > mapping :: DomGen -> Mapping
-- > mapping (t, s, s') : gens = (s,s') : mapping gens

\end{code}

Analogical transfer

Helper functions for collecting up the substitutions from a generalized domain

\begin{code}

 targetSubsOf :: [Gen] -> [Sub] -- collects all the ``right projections'', the substitutions to the target domain
 targetSubsOf [] = []
 targetSubsOf gens = map third gens where
   third :: (a, b, c) -> c
   third (_,_,x) = x

 sourceSubsOf :: [Gen] -> [Sub] -- collects all the ``left projections'', the substitutions to the source domain
 sourceSubsOf [] = []
 sourceSubsOf gens = map second gens where
   second :: (a, b, c) -> b
   second (_,x,_) = x

 instanceOfSub :: Form -> Sub
 instanceOfSub = undefined

--  --          generalized domain -> analogical pairs (s,t'), where t' is the expanded target domain 
--  transfer :: DomGen -> [(Form, Form)]
--  transfer [] = []
--  transfer ((g, s, t):gens) = (apply s g, f::Form) : transfer gens

-- --          generalized domain -> analogical pairs (s,t'), where t' is the expanded target domain 
-- transfer :: [Gen] -> [(Form, Form)]
-- transfer gens = [ (apply s g, apply t' g) | (g, s, _) <- gens, (_, _, t') <- gens ]


\end{code}

Now we check a list of lggs and measure their relative complexities

\begin{code}
 type Comp = Int

-- Complexity of one simple substitution

 cSimple :: Sub -> Comp
 cSimple (SR r) = 0
 cSimple (SF f) = 1
 cSimple (SI (AI (f, f', g, i))) = length (fst (symbAr(VS g))) + 1  ---- We look at the length of the arity of G (the variable we wish to insert)
 cSimple (SP p) = 1

-- Complexity of a list of substitutions
 cList :: [Sub] -> Comp
 cList [] = 0
 cList (x:xs) = cSimple x + cList xs 

-- test with: cList [SP $ P ("F", "G", fun), SP $ P ("W", "G", fun), SF $ F ("X", "sun"), SR $ R ("X", "Z"), SI $ AI ("F", "F", "W", 2)]


-- Complexity of a generalisation (taken as a triple of a term and two lists of substituations)

 cGen :: (Term, [Sub], [Sub]) -> Comp
 cGen (t, s, s') = cList s + cList s'

 prefGen :: [(Term, [Sub], [Sub])] -> (Term, [Sub], [Sub])
 prefGen [x] = x
 prefGen (x:xs) | cGen x <= cGen (prefGen xs) = x
                | otherwise = prefGen xs

 mySubs = [SP $ P ("F", "G", fun), SP $ P ("W", "G", fun), SF $ F ("X", "sun"), SR $ R ("X", "Z"), SI $ AI ("F", "F", "W", 2)]
 mySubs2 = [SP $ P ("F", "G", fun), SF $ F ("X", "sun"), SI $ AI ("F", "F", "W", 2)]

 myterm = T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") [] ]

 -- test with: prefGen [(myterm, mySubs, mySubs), (myterm, mySubs2, mySubs2)]

 -- output is (myterm, mySubs2, mySubs2)

\end{code}