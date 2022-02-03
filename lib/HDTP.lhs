\begin{code}
 module HDTP where
 import Data.List ((\\), find, sortBy)

 -- TODO we need this for the test, move it somewhere
 instance Show (a -> b) where
        show a = "function"

 instance Eq (a -> b) where
        (==) _ _ = True
\end{code}

\section{First-Order Theories and Basic Types}

Unlike other models of analogical reasoning (see e.g. \cite{Hofstadter1995TheCP}, \cite{Gentner1983StructureMappingAT}), but in line with broader trends in the cognitive science literature, HDTP represents an agent's knowledge of any given domain of knowledge as a finite, multi-sorted, first-order theory. In order to implement this in Haskell, we first need to define things from the ground up.  
% \input{lib/Basics.lhs}
Classically, a first-order language $\mathcal{L}$ is a set of formulae built out of... The particular formulation written below draws heavily from the formalization presented in \cite{Schwering2009SyntacticPO}:

\begin{definition}[Signature]
    We define a signature to be a 5-tuple \\$\Sigma = (Sort_\Sigma, Func_\Sigma, Pred_\Sigma, arP, arF)$, where 
    \begin{itemize}
        \item $Sort_\Sigma$ is a set of \textit{sorts};
        \item $Func_\Sigma$ is a set of \textit{function symbols};
        \item $Pred_\Sigma$ is a set of \textit{predicate symbols};
        \item $arP: Pred_\Sigma \to Sort_\Sigma^*$ is an \textit{arity function} on predicate symbols, giving each predicate symbol its arity; 
        \item $arF: Func_\Sigma \to Sort_\Sigma^* \times Sort_\Sigma$ is an \textit{arity function} on functions, sending each function symbol to its domain and codomain.
    \end{itemize} 
\end{definition}


\begin{code}
 type FunSymb = String
 newtype PredSymb = PS String deriving (Eq, Show)
 type VarSymb = String
 newtype Sort = S String deriving (Eq, Show)
\end{code}


Now if we 
\begin{definition}[Terms]
    Let $V = \{v_1 : s, v_2 : s \dots \}$ be an infinite set of sorted variables, and $\Sigma$ a signature. We can define a term algebra $Term(\Sigma, V)$ recursively as the smallest set obeying the following conditions:
    \begin{enumerate}[label=(\arabic*)]
        \item If $x :s \in V$, then $x \in Term(\Sigma, V)$.
        \item If $f : s_1 \times \dots s_n \to s \in Func_\Sigma$, and $t_1 : s_1, \dots t_n :s_n \in Term(\Sigma, V)$, then \\$f(t_1, \dots t_n) : s \in Term(\Sigma, V)$.
    \end{enumerate}
\end{definition}

\begin{definition}[Formula]
    Given signature $\Sigma$ and term algebra $Term(\Sigma, V)$, we can define the set of formulae over $\Sigma$ and $V$, $Form(\Sigma, V)$ recursively as the smallest set obeying the following conditions:
    \begin{enumerate}
        \item If $p : s_1 \times s_n \in Pred_\Sigma$, and $t_1 : s_1, \dots t_n :s_n \in Term(\Sigma, V)$, then $p(t_1, \dots, t_n) : s \in Form(\Sigma, V)$.
        \item If $\alpha, \beta \in Form(\Sigma, V)$, then $\neg \alpha, \alpha \lor \beta, \forall x_i : s_i\  (\alpha) \in Form(\Sigma, V)$.
    \end{enumerate}
\end{definition}

TODO Xavier explain how we manage arity and how we use it as a database

\begin{code}
 -- newtype Term Sg [[s], [f], [p], af, ap] [v] = v | f [Term] deriving (Eq,Ord,Show)
 data TSymb = VS VarSymb | FS FunSymb deriving (Eq, Show)
 data Term = T TSymb [Term] deriving (Eq, Show) -- Find a way to restrict this to respect sorts
 data Form = FT PredSymb [Term] | Not Form | Disj Form Form | Forall VarSymb Form deriving (Eq, Show)

 symbAr :: TSymb -> ([Sort], Sort)
 symbAr (VS "F") = ([S "a"], S "b")
 symbAr (VS "F'") = ([S "a"], S "b")
 symbAr (VS "G") = ([S "a"], S "b")
 symbAr (VS "W") = ([S "a"], S "b")
 symbAr _ = undefined
 predAr :: PredSymb -> [Sort]
 predAr = undefined

\end{code}

In Haskell, TODO

Finally, with all of these preliminaries in place, we can define the basic unit of knowledge in HDTP, the domain:

\begin{definition}[Domain]
    We define a \textit{domain} to be a finite set of formulae $\mathcal{D}_\alpha = \{\alpha_1, \dots \alpha_n\}$ (where $\alpha_i \in \mathcal{L}_\Sigma$) closed under logical consequence.
\end{definition}

\begin{code}
 type Domain = [Form]
\end{code}


\section{Anti-Unification and Least General Generalization}
The proper identification of common structure between seemingly disparate domains of knowledge is an essential ingredient of analogical reasoning, and as HDTP represents domains as sets of first-order formulae, what is needed is a well-defined notion of shared structure in formulae.



Originally proposed in \cite{Plotkin70}, generalization (also known as anti-unification) is just such a notion: an anti-unifier of any two terms $s,t$ is a term containing only their shared syntactic structure: the distinguishing details of $s$ and $t$ have been abstracted away by replacing the constants with variables. More formally:

\begin{definition}[First-order Generalization]
    Let $s, t$ be first-order terms (resp. formulae). A \textit{generalization} is a triple $g = \langle a, \sigma, \tau \rangle$ with term (resp. formula) $a$ and substitutions $\sigma, \tau$ such that $s \xleftarrow{\sigma} a \xrightarrow{\tau} t$.
    We say that $a$ is an \textit{anti-unifier} of $\{s,t\}$.
\end{definition}


\begin{definition}[First-order Substitution on Variables]
    
\end{definition}


By themselves, generalizations aren't necessarily helpful. A generalization that removes too much detail leaves us with a term devoid of any real content.

For example, let $s := 2+6$ and $t:= 3+6$. If we consider the anti-unifer $a:= x+y$ in generalization $g = \langle x+y, (x \mapsto 2, y \mapsto 6), (x\mapsto 3, y \mapsto 6)\rangle$, we can see that while $g$ is most certainly \textit{a} generalization of $s,t$, it is one which has abstracted away too much information, as it has failed to notice that both $s$ and $t$ are terms in which $6$ is being added to another number. Instead, the generalization $g$ is only capable of showing that \textit{some} numbers are being added together. 

What's needed to get around this is some notion of minimality:

\begin{definition}[Least General Generalization]
    For terms $s,t$, we call a generalization $g = \langle a, \sigma, \tau \rangle$ the \textit{least general generalization (lgg)}, if for every generalization $g' = \langle a', \sigma', \tau' \rangle$, there exists a (unique) substitution $\gamma : a' \to a$ such that $\sigma' = \sigma \circ \gamma$ and $\tau' = \tau \circ \gamma$.\quad We say that $a$ is the \textit{most specific anti-unifier} of $\{s,t\}$.
\end{definition}


In this way, least general generalizations constitute limits in the category of first-order substitutions. As proven in \cite{Plotkin70}, this category has all finite limits: for any finite set of first-order terms, one can always find a lgg.

In the original 1970 paper, this result was shown constructively with an imperative algorithm. Helpfully for us, a functional algorithm to do the same is detailed in \cite{Tabareau2013AntiUnificationWT}.


\begin{code}
 -- Produces a VarSymb NOT in the provided list. Works for any number of variables.
 -- we exploit haskell's lazyness, we just take the first string of the infinite list of all possible strings that are not in the list given as argument
 -- we add X,Y,Z,W at the beginning of the infinite list of all possible variable names because those are our preferred names
 newVariable :: [VarSymb] -> VarSymb
 newVariable xs = head (allVarSymb \\ xs) where 
    allVarSymb = ["X","Y","Z","W"] ++ [ c : s | s <- "": allVarSymb, c <- ['A'..'Z']]


 sameTop :: [Term] -> [Term] -> [Subs] -> [(Term, [Subs])]
 sameTop [] [] theta = []
 sameTop (u:us) (t:ts) theta = lambdaOfTerms : sameTop us ts (snd lambdaOfTerms) where
                                    lambdaOfTerms = lambdaForTerms u t theta

 lambdaForTerms :: Term -> Term -> [Subs] -> (Term, [Subs])
 lambdaForTerms t u theta | t == u = (t, theta) -- Boring case
 lambdaForTerms (T (FS f) ts) (T (FS f') us) theta | f == f' = (T (FS f) (map fst termSubsList)  , snd (last termSubsList)) where -- Same top constructor case 
                                                        termSubsList = sameTop ts us theta 
 lambdaForTerms t u theta = case find (\(_, t', u') -> t == t' && u == u') theta of
   Just (x, _, _) -> (T (VS x) [], theta)
   Nothing -> (T (VS x) [], (x, t, u):theta) where x = newVariable (map (\(x, _, _) -> x) theta)

-- (a -> Bool) -> [a] -> Maybe a
 lambda :: Form -> Form -> [Subs] -> (Form, [Subs])
 lambda phi psi theta | phi == psi = (phi, theta)
 lambda (FT ps ts) (FT ps' us) theta | ps == ps' = (FT ps (map fst prSubsList)  , snd (last prSubsList)) where -- Same top constructor case  
                                                        prSubsList = sameTop ts us theta 
 lambda (Not phi) (Not psi) theta = (Not outForm, subs) where (outForm, subs) = lambda phi psi theta
 lambda (Disj phi phi') (Disj psi psi') theta = (Disj outForm outForm', subs ++ subs') where
   (outForm, subs) = lambda phi psi theta
   (outForm', subs') = lambda phi' psi' theta
 lambda (Forall vs form) (Forall vs' form') theta = undefined -- TODO
 lambda _ _ _ = undefined

\end{code}


\section{Basic Substitutions and Not Too General Generalizations}

While first-order anti-unification is useful for many purposes, it isn't strong enough to capture similarities which humans regularly can when forming analogies. For example, consider terms $s:= 2+3$ and $t:= 2\times 3$. Using only first-order substitutions, the lgg of $\{s,t\}$ is simply $g = \langle x, x\mapsto 2+3, x\mapsto 2 \times 3\rangle$. Because first-order substitutions cannot instantiate function symbols, the obvious generalization is not found.

\subsection{Basic Substitutions}
% \input{test/simpletests.lhs}
To better capture these kinds of situations, HDTP replaces the simple form of first-order substitutions with four so-called ``basic substitutions'', functions $bs : Term(\Sigma, V) \to Term(\Sigma, V)$ which allow for some second-order properties. 

Following what appears to be the authors' intent, we can generalize these basic substitutions to apply to formulae. Our implementation of these substitutions ...


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

 apply' :: [Sub] -> Form -> Form
 apply' subs phi = foldr apply phi subs
\end{code}

\begin{definition}[Renaming]
    A \textit{renaming} $\rho^F_{F'}$ replaces a variable $F : s_1 \times \dots \times s_n \to s \in V_n$ with a variable $F' : s_1 \times \dots \times s_n \to s \in V_n$ $$F(t_1 : s_1, \dots t_n : s_n) : s \xrightarrow{\rho^F_{F'}}F'(t_1 : s_1, \dots t_n : s_n) : s$$
\end{definition}

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

\begin{definition}[Fixation]
    A \textit{fixation} $\phi^F_f$ replaces a variable $F : s_1 \times \dots \times s_n \to s \in V_n$ with a function symbol $f : s_1 \times \dots \times s_n \to s \in Func_\Sigma$ $$F(t_1 : s_1, \dots t_n : s_n) : s \xrightarrow{\phi^F_f}f(t_1 : s_1, \dots t_n : s_n) : s$$
\end{definition}

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

\begin{definition}[Argument Insertion]
    An \textit{argument insertion} $\iota^{F,F'}_{G,i}$, with $0 \le o \le n$, $F : s_1 \times \dots \times s_n \to s \in V_n$, $G : s_i \times \dots \times s_{i+k-1} \to s_g \in V_k$ with $k \le n - i$ and $F' : s_1 \times \dots \times s_{i-1} \times s_g \times s_{i+k} \times \dots \times s_n \to s \in V_{n-k+1}$ is defined as: 
    \begin{align*}
        &F(t_1 : s_1, \dots t_n : s_n) : s \xrightarrow{\phi^F_f}\\
        F'(t_1 : s_1,  \dots t_{i-1} : s_{i-1}, & G (t_i : s_i, \dots, t_{i+k-1} : s_{i+k-1}) : s_g, t_{i+k} : s_{i+k}, \dots, t_n : s_n) :s
    \end{align*}
\end{definition}

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

\begin{definition}[Permutation]
    A \textit{permutation} $\pi^{F,F'}_{\alpha}$ with variables $F : s_1 \times \dots \times s_n \to s \in V_n$ and $F' : s_1 \times \dots \times s_n \to s \in V_n$, together with a bijective function $\alpha : \{1, \dots, n\} \to \{1, \dots, n\}$ (which is not the identity function), rearranges the arguments of a term:
    $$F(t_1 : s_1, \dots t_n : s_n) : s \xrightarrow{\pi^{F,F'}_{\alpha}} F'(t_{\alpha(1)} : s_{\alpha(1)}, \dots t_{\alpha(n)} : s_{\alpha(n)}) : s$$
\end{definition}

\begin{code}


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



\subsection{LGGs and the Basic Substitutions}
The authors of \cite{Schmidt-2014} claim that once we allow for restricted
higher-order substitution, we can no longer speak of a single least general
generalization. This claim presents a number of issues. First, lggs, as
defined in \cite{Plotkin70}, are necessarily unique. When this uniqueness
property is removed, it isn't clear what precisely the authors mean when they
refer to an lgg. Second, due to this problem of definition, it is difficult
to verify any relationship between higher-order substitutions and the
uniqueness of lggs. The authors provide no proof, nor can one be found in a
search of related literature (\cite{Krumnack2007RestrictedHA},
\cite{Schwering2009SyntacticPO}). The closest we find to a justification of
this claim is a figure on page 174 of \cite{Schmidt-2014}, in which the
authors claim that the pair of terms below $$f (g(a, b, c), d),\quad f (d, h (a))$$
have three most specific anti-unifiers: $$f (X, Y ), \quad F (d,G(a)) \quad F'(G(a), d)$$
How these all three of these terms can be \textit{the} most specific anti-unifier of the pair of terms above is not entirely clear.

In lieu of more clarity from the literature, we can only attempt to provide a
new definition that we hope might be a better fit for the authors'
intuitions. First, we can define generalizations as we expect the authors
intend:

\begin{definition}[Restricted Second-Order Generalization]
    Let $s, t$ be first-order terms (resp. formulae). A \textit{restricted second-order generalization} (rsog) is a triple $g = \langle a, \sigma, \tau \rangle$ where $a$ is a term (resp. formula) $a$ and $\sigma, \tau$ are of the form $bs_1 \circ \dots \circ bs_n$ where for $1 \le i \le n$, $bs_i$ is a basic substitution, and such that $s \xleftarrow{\sigma} a \xrightarrow{\tau} t$.
    We say that $a$ is an \textit{anti-unifier} of $\{s,t\}$.
\end{definition}
Next, as lggs constitute limits in the category of substitutions, and the authors appear to be speaking of sets of lggs, we're reminded of the categorical notion of a \textit{multi-limit}:

\begin{definition}[Multi-Lgg]
    For terms $s,t$, we define a \textit{multi-lgg} to be a set of tuples $ML = \{ \langle a_1, \sigma_1, \tau_1 \rangle, \dots, \langle a_n, \sigma_n, \tau_n \rangle\}$ such that, for every generalization $g' = \langle a', \sigma', \tau' \rangle$, there exists a (unique) chain of basic substitutions $\gamma : a' \to a_i$ for a unique $a_i \in ML$, such that $\sigma' = \sigma_i \circ \gamma$ and $\tau' = \tau_i \circ \gamma$.
\end{definition}

Proving whether first-order terms and chains of basic substitutions
constitute a category, or whether multi-lggs can indeed be constructed
for any set of first-order terms, is unfortunately beyond the scope of
the current report. We include these remarks only for the purpose of
guiding future research. 

In the present work, we shall continue by proposing an algorithm to
produce restricted second-order generalizations which are helpfully
specific, something we will call \textit{not too general
generalizations}, or \textit{ntgg}s for short.

\begin{definition}[Not Too General Generalization]
    For terms $s,t$, we call a rsog $g = \langle a, \sigma, \tau \rangle$ a \textit{not too general generalization (ntgg)}, if for some suitably large number of rsogs $g' = \langle a', \sigma', \tau' \rangle$, there exists a chain of basic substitutions $\gamma : a' \to a$ such that $\sigma' = \sigma \circ \gamma$ and $\tau' = \tau \circ \gamma$.\quad We say that $a$ is the \textit{specific enough anti-unifier} of $\{s,t\}$.
\end{definition}

Obviously, the use of the term ``suitably large'' in this definition is not as precise as could be hoped for, but for the present report, this level of vagueness is useful. 

\subsection{Generating NTGGs}
As a compromise between taking advantage of the existing literature
and accounting for the needs of HDTP, we have attempted to re-purpose
the algorithm in \cite{Tabareau2013AntiUnificationWT} to create our
ntggs.


\subsection{Alignments, Complexity of NTGGs, and Domain Generalizations}
To create an analogy between two domains, there needs to be a method
for selecting which formulae from the source domain should be seen as
analogous to which formulae in the target domain. \cite{Schmidt-2014}
calls for a process for generating an \textit{alignment} between
domains:

\begin{definition}[Alignment]
    Given two domains $\mathcal{D}_\alpha, \mathcal{D}_\beta$, an \textit{alignment} is a set of pairs of formulae $[\langle \alpha_1, \beta_1\rangle, \dots, \langle \alpha_n, \beta_n\rangle ]$, with $\alpha_i \in \mathcal{D}_\alpha$ and $\beta_i \in \mathcal{D}_\beta$.
\end{definition} 

The algorithm in place so far simply finds an ntgg for every pair of
formulae $(\alpha, \beta) \in \mathcal{D}_\alpha \times
\mathcal{D}_\beta$. What is needed is a means to find the
``best-fitting'' pairs of formulae. We will do so by making use of the
notion of ``complexity of generalization'' discussed in
\cite{Schmidt-2014}:

\begin{definition}[Complexity of Substitutions]
    We define the complexity of a basic substitution $bs$ as:
    \begin{equation}
    \mathcal{C}(bs) =
    \begin{cases*}
      0 & \text{if} bs \text{is a renaming} \\
      1 & \text{if} bs \text{is a fixation} \\
      k+1 & \text{if} bs \text{is an argument insertion, and}\\
       \quad \text{the inserted argument is a variable of arity k} \\
      1 & \text{if} bs \text{is a permutation} \\
    \end{cases*}
  \end{equation}
  
  The complexity of a composition of basic substitutions is simply the sum of each basic substitution composed:
  $$\mathcal{C}(bs_1 \circ \dots \circ bs_n) = \displaystyle \sum_{i= 1}^n \mathcal{C}(bs_i) $$
\end{definition}

\begin{definition}[Complexity of Generalizations]
    Let $g = \langle a, \sigma, \tau \rangle$ be an ntgg for a pair of terms $\{s,t\}$. We define the complexity of $g$ as $\mathcal{C}( \langle a, \sigma, \tau \rangle) = \mathcal{C}(\sigma) + \mathcal{C}(\tau)$. 
\end{definition}


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
 cList xs = foldr ((+) . cSimple) 0 xs


-- test with: cList [SP $ P ("F", "G", fun), SP $ P ("W", "G", fun), SF $ F ("X", "sun"), SR $ R ("X", "Z"), SI $ AI ("F", "F", "W", 2)]

-- Complexity of a generalisation (taken as a triple of a term and two lists of substituations) we need to fix this to fit the definition from above

 cGen :: Gen -> Comp
 cGen (_, s, s') = cList s + cList s'

 prefGen :: [Gen] -> Gen
 prefGen [x] = x
 prefGen (x:xs) | cGen x <= cGen (prefGen xs) = x
                | otherwise = prefGen xs

 mySubs = [SP $ P ("F", "G", fun), SP $ P ("W", "G", fun), SF $ F ("X", "sun"), SR $ R ("X", "Z"), SI $ AI ("F", "F", "W", 2)]
 mySubs2 = [SP $ P ("F", "G", fun), SF $ F ("X", "sun"), SI $ AI ("F", "F", "W", 2)]

 myterm = T (VS "F") [T (VS "Y") [], T (VS "X") [], T (VS "T") []]

 -- test with: prefGen [(myterm, mySubs, mySubs), (myterm, mySubs2, mySubs2)]

 -- output is (myterm, mySubs2, mySubs2)

\end{code}

The intuition for this measure, as described in the original work, is that human subjects appear to have a bias towards substitutions which 


With a metric in place for comparing the desirability of different ntggs, we can select the ``best'' alignment as the one whose generalizations are least costly:



This notion is different to the definition of ``Preferred Generalization'' given in \cite{Schmidt-2014}, as it's actually well-defined, you fucks!

Now, we finally have all the pieces in place to construct the basic framework for forming an analogy between two domains, \cite{Schmidt-2014}'s \textit{domain generalization}:

\begin{definition}[Domain Generalization]
    Given an alignment $[\langle \alpha_1, \beta_1\rangle, \dots, \langle \alpha_n, \beta_n\rangle ]$, a \textit{domain generalization} is a set of ntggs $ \mathcal{D}_g = [ g_1, \dots g_n ]$, where for $1 \le i \le n$, $g_i = \langle a_i, \sigma_i, \tau_i\rangle$ such that $\alpha_i \xleftarrow{\sigma_i} a_i \xrightarrow{\tau_i} \beta_i$.
\end{definition}


\begin{code}
 type Align = [(Form, Form)]


-- type Gen = (Form, [Sub], [Sub])
-- type Subs = (VarSymb, Term, Term)

 -- Calculate all the NTGGs from all possible pairs between the source domain (of size n) and the target domain (of size m), and then pick the m pairs with the lowest complexity
 -- output: [(0,1,2,3,4)] such that 2 <-1- 0 -3-> 4
 align :: Domain -> Domain -> [(Form, [[Sub]], Form, [[Sub]], Form)]
 align d d' = take (length d') $ sortBy (\p p' -> complexity p `compare` complexity p') [ result phi psi | phi <- d, psi <- d' ] where
   complexity (_, subPhi, _, subPsi, _) = cList (concat subPhi) + cList (concat subPsi)
   result phi psi = (antiUnifier, sourceSubsOf $ map (subsToGen phi) subs, phi, targetSubsOf $ map (subsToGen psi) subs, psi) where
     (antiUnifier, subs) = lambda phi psi []
\end{code}


\begin{code}
 type Gen = (Form, [Sub], [Sub])
 type Subs = (VarSymb, Term, Term)

 -- First argument: the "context" formula in which we apply the second argument
 -- Second argument: t <- x -> u
 -- Result: the context formula and the corresponding substitutions in it
 subsToGen :: Form -> Subs -> Gen
 subsToGen context (vs, t, u) = (context, subsToGenHelper context vs t, subsToGenHelper context vs u)

 -- Variables in a given term
 varsIn :: Form -> [VarSymb]
 varsIn (FT (PS _) ts) = concatMap varsInTerm ts
 varsIn (Not phi) = varsIn phi
 varsIn (Disj phi psi) = varsIn phi ++ varsIn psi
 varsIn (Forall _ phi) = varsIn phi -- TODO ?

 varsInTerm :: Term -> [VarSymb]
 varsInTerm = undefined

 -- First argument: the "context" formula in which we apply the second and third argument
 -- Second argument: x
 -- Third argument: t
 -- Result: the (chain of) substitutions that result in x -> t inside of context
 subsToGenHelper :: Form -> VarSymb -> Term -> [Sub]
 subsToGenHelper phi vs (T (FS fs) ts) = SF (F (newVar, fs)) : subsToGenHelperRec (newVar:varsIn phi) vs (T (VS newVar) ts) where
   newVar = newVariable (varsIn phi)
 subsToGenHelper _ _ _ = undefined -- TODO

 subsToGenHelperRec :: [VarSymb] -> VarSymb -> Term -> [Sub]
 subsToGenHelperRec vars vs (T (VS vs') (T (FS fs) _:ts)) = SF (F (newVar, fs)) : SI (AI (newVar', vs', newVar, 0)) : subsToGenHelperRec (newVar':newVar:vars) vs (T (VS vs') ts) where
   newVar = newVariable vars
   newVar' = newVariable (newVar:vars)
 subsToGenHelperRec _ vs (T (VS vs') []) = [SR (R (vs, vs'))]
 subsToGenHelperRec _ _ _ = undefined -- TODO which cases can actually happen?

-- gnrlz :: Term -> Term -> Gen
-- gnrlz s t = (g)

\end{code}


\section{Analogical Transfer}
As stated previously, the ultimate purpose of generalizations is to allow an agent to form analogies between two domains of knowledge, and then to leverage her knowledge of the source domain to infer new formulae in the target domain. The present section will detail how we model this process in our Haskell implementation of HDTP.
% \input{Profiling.tex}

For the most part, \cite{Schmidt-2014} provides few details about analogical transfer in HDTP, but drawing on sources such as \cite{Schwering2009SyntacticPO}, we can infer that analogical transfer is meant to be the composition of two chains of substitutions: first, for any given formula in the source domain $\alpha_i \in \mathcal{D}_\alpha$, apply $\sigma_i^{-1} : \alpha_i \to a_i$ to ``send'' $\alpha_i$ to its specific enough anti-unifier in the domain generalization $a_i \in \mathcal{D}_g$.
Second, apply any number of the chains of substitutions $\{\tau_1, \dots \tau_n\}$ in $\mathcal{D}_g$ in order to produce a new formula $\beta \in \mathcal{D}_\beta$ in the target domain.

In our implementation of analogical transfer, we have chosen to freely generate all sentences about from the TODO


\begin{code}

 targetSubsOf :: [Gen] -> [[Sub]] -- collects all the ``right projections'', the substitutions to the target domain
 targetSubsOf [] = []
 targetSubsOf gens = map third gens where
   third :: (a, b, c) -> c
   third (_,_,x) = x

 sourceSubsOf :: [Gen] -> [[Sub]] -- collects all the ``left projections'', the substitutions to the source domain
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
 transfer :: [Gen] -> [(Form, Form)]
 transfer gens = [ (apply' s g, apply' t' g) | (g, s, _) <- gens, (_, _, t') <- gens ]


\end{code}
