TODO kill all warnings -Wall
TODO kill all lint notices

\begin{code}
 module HDTP where
 import Data.List ((\\), find, sortBy)
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

% TODO: page number in citation

In the original 1970 paper, this result was shown constructively with an imperative algorithm. Helpfully for us, a functional algorithm to do the same is detailed in \cite[3]{Tabareau2013AntiUnificationWT}. It runs as follows.

$
\begin{aligned}
    \lambda(t,t,\theta) & = (t, \theta))  \\
    \lambda(f(t_1,\dots,t_n), f(u_1,\dots,u_n), \theta_0) & = (f(x_1, \dots, x_n), \theta_n)) & \text{where } \lambda(t_i, u_i, \theta_{i-1}) = (x_i, \theta_i) \\
    \lambda(t,u,\theta) & = (x, \theta)) & \text{if } \theta(x) = (t,u) \\
    \lambda(t,u,\theta) & = (y, \theta ') & \text{ where } y \notin \text{dom} (\theta) \text{ and } \theta' = \theta + \{y \mapsto (t,u)\} \\ \\
    \texttt{leastGen}(t,u) & = \pi_1(\lambda(t,u, \{\}))
\end{aligned}
$


To implement this algorith in Haskell, we first implement a helper function which takes a list of variable symbols and gives us a new variable name that is not yet in that list. Exploiting Haskell's lazyness this function can create new variable names for a given list of any length. We first add $X, Y, Z, W$ to the list of possible variable symbols as those are our preferred variable names.

\begin{code}
 newVariable :: [VarSymb] -> VarSymb
 newVariable xs = head (allVarSymb \\ xs) where 
    allVarSymb = ["X","Y","Z","W"] ++ [ c : s | s <- "": allVarSymb, c <- ['A'..'Z']]
\end{code}



\begin{code}

 lambdaForTerms :: Term -> Term -> [TermGen] -> (Term, [TermGen])
 lambdaForTerms t u theta | t == u = (t, theta) -- Boring case
 lambdaForTerms (T (FS f) ts) (T (FS f') us) theta | f == f' = (T (FS f) (map fst termSubsList), snd (last termSubsList)) where 
   termSubsList = sameTop ts us theta
 lambdaForTerms t u theta = case find (\(_, t', u') -> t == t' && u == u') theta of
   Just (x, _, _) -> (T (VS x) [], theta)
   Nothing -> (T (VS x) [], (x, t, u):theta) where x = newVariable (map (\(x, _, _) -> x) theta)

\end{code}

Here we use the helper function\texttt{sameTop} that takes two lists of terms and a list of generalisations and feeds the i-th

\begin{code}
 sameTop :: [Term] -> [Term] -> [TermGen] -> [(Term, [TermGen])]
 sameTop [] [] theta = []
 sameTop (u:us) (t:ts) theta = lambdaOfTerms : sameTop us ts (snd lambdaOfTerms) where
                                    lambdaOfTerms = lambdaForTerms u t theta

\end{code}

The original algorithm from (TODO quote Tabareau) is designed for generalizing terms, not formulas.
We have adapted it to pairs of general formulas, provided that they have the same predicate structure.

\begin{code}

 lambda :: Form -> Form -> [TermGen] -> (Form, [TermGen])
 lambda phi psi theta | phi == psi = (phi, theta)
 lambda (FT ps ts) (FT ps' us) theta | ps == ps' = (FT ps (map fst prSubsList), snd (last prSubsList)) where 
                                                        prSubsList = sameTop ts us theta
 lambda (Not phi) (Not psi) theta = (Not outForm, subs) where (outForm, subs) = lambda phi psi theta
 lambda (Disj phi phi') (Disj psi psi') theta = (Disj outForm outForm', subs ++ subs') where
   (outForm, subs) = lambda phi psi theta
   (outForm', subs') = lambda phi' psi' theta
 lambda (Forall vs phi) (Forall _ psi) theta = (Forall vs outForm, subs) where (outForm, subs) = lambda phi psi theta
 lambda _ _ _ = undefined -- We only anti-unify formulas that have the same predicate structure

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
 apply r (Forall w form) = Forall w (apply r form)

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

In Haskell, we implement fixations as follows.

\begin{code}
 newtype Fixation = F (VarSymb, FunSymb) deriving (Eq, Show)

 applyFixation :: Fixation -> Form -> Form
 applyFixation (F (v, f)) (FT p ts) = FT p (map fixInTerm ts) where
   fixInTerm :: Term -> Term
   fixInTerm (T (VS w) ts') | w == v = T (FS f) ts'
                            | otherwise = T (VS w) ts'
   fixInTerm (T (FS f') ts') = T (FS f') (map fixInTerm ts')
 applyFixation _ _ = undefined -- Recursive cases handled by apply

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

\end{code}

\begin{definition}[Permutation]
    A \textit{permutation} $\pi^{F,F'}_{\alpha}$ with variables $F : s_1 \times \dots \times s_n \to s \in V_n$ and $F' : s_1 \times \dots \times s_n \to s \in V_n$, together with a bijective function $\alpha : \{1, \dots, n\} \to \{1, \dots, n\}$ (which is not the identity function), rearranges the arguments of a term:
    $$F(t_1 : s_1, \dots t_n : s_n) : s \xrightarrow{\pi^{F,F'}_{\alpha}} F'(t_{\alpha(1)} : s_{\alpha(1)}, \dots t_{\alpha(n)} : s_{\alpha(n)}) : s$$
\end{definition}

We define permutations as follows in Haskell.

TODO justify why we need the instances Show, Eq for function

\begin{code}
 instance Show (a -> b) where
   show _ = "function"

 instance Eq (a -> b) where
   (==) _ _ = True

 newtype Permutation = P (VarSymb, VarSymb, Int -> Int) deriving (Eq, Show)

\end{code}

 %-- Here it must hold that f assigns only indices smaller than length of the list to such indices, no checking whether f is bijective is done

The following recursive helper function permutes a list, given a function from indices of that list to indices of that list. Because of the recursive charcater of this helper function the list needs to be given twice as an argument.

\begin{code}
 
 permute :: [a] -> [a] -> (Int -> Int) -> [a]
 permute [] l f = []
 permute (x:xs) l f = l!!f (length l - (length xs + 1)) : permute xs l f

\end{code}

The following function allows then to apply a permutation to a formula. 

\begin{code}

 applyPermutation :: Permutation -> Form -> Form
 applyPermutation p (FT pr ts) = FT pr (map (permInTerm p) ts) where
   permInTerm :: Permutation -> Term -> Term
   permInTerm (P (v, v', f)) (T (VS w) ts) | v == w = T (VS v') (permute ts ts f) 
                                           | otherwise = T (VS w) ts
   permInTerm r (T (FS f) ts) = T (FS f) (map (permInTerm r) ts)
 applyPermutation _ _ = undefined -- Recursive cases handled by apply

\end{code}

%  perm :: Permutation
%  perm = P ("X", "Y", fun) 

%  -- to test: this is basically a formula P(X(a,b,c)). a,b,c are constants (zero-ary functions)
%  someForm :: Form
%  someForm = FT (PS "P") [T (VS "X") [ T (FS "a") [], T (FS "b") [], T (FS "c") []]]

%  -- Output: FT (PS "P") [T (VS "X") [T (FS "b") [],T (FS "c") [],T (FS "a") []]]
%  ppp :: Form
%  ppp = apply (SP perm) someForm



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
 cSimple (SR _) = 0
 cSimple (SF _) = 1
 cSimple (SI (AI (_, _, g, _))) = length (fst (symbAr(VS g))) + 1  ---- We look at the length of the arity of G (the variable we wish to insert)
 cSimple (SP _) = 1

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

\end{code}

%  -- test with: prefGen [(myterm, mySubs, mySubs), (myterm, mySubs2, mySubs2)]

%  -- output is (myterm, mySubs2, mySubs2)

The intuition for this measure, as described in the original work, is that human subjects appear to have a bias towards substitutions which 


With a metric in place for comparing the desirability of different ntggs, we can select the ``best'' alignment as the one whose generalizations are least costly:



This notion is different to the definition of ``Preferred Generalization'' given in \cite{Schmidt-2014}, as it's actually well-defined, you fucks!

Now, we finally have all the pieces in place to construct the basic framework for forming an analogy between two domains, \cite{Schmidt-2014}'s \textit{domain generalization}:

\begin{definition}[Domain Generalization]
    Given an alignment $[\langle \alpha_1, \beta_1\rangle, \dots, \langle \alpha_n, \beta_n\rangle ]$, a \textit{domain generalization} is a set of ntggs $ \mathcal{D}_g = [ g_1, \dots g_n ]$, where for $1 \le i \le n$, $g_i = \langle a_i, \sigma_i, \tau_i\rangle$ such that $\alpha_i \xleftarrow{\sigma_i} a_i \xrightarrow{\tau_i} \beta_i$.
\end{definition}


\begin{code}

 -- Calculate all the NTGGs from all possible pairs between the source domain (of size n) and the target domain (of size m), and then pick the m pairs with the lowest complexity
 -- output: [(0,1,2,3,4)] such that 2 <-1- 0 -3-> 4
 align :: Domain -> Domain -> [(Form, [Sub], Form, [Sub], Form)]
 align d d' = take (length d') $ sortBy (\p p' -> complexity p `compare` complexity p') [ result phi psi | phi <- d, psi <- d' ] where
   complexity (_, subPhi, _, subPsi, _) = cList subPhi + cList subPsi
   result phi psi = (antiUnifier, concat $ sourceSubsOf $ map (termToFormGen phi) subs, phi, concat $ targetSubsOf $ map (termToFormGen psi) subs, psi) where
     (antiUnifier, subs) = lambda phi psi []

 alignsToTransfers :: [(Form, [Sub], Form, [Sub], Form)] -> [Gen]
 alignsToTransfers = map alignToTransfer where
   alignToTransfer :: (Form, [Sub], Form, [Sub], Form) -> Gen
   alignToTransfer (antiUnifier, subPhi, _, subPsi, _) = (antiUnifier, subPhi, subPsi)

\end{code}


\begin{code}
 type Gen = (Form, [Sub], [Sub])
 -- Term generalization from Tabareau
 type TermGen = (VarSymb, Term, Term)

 -- Variables in a given form
 varsInForm :: Form -> [VarSymb]
 varsInForm (FT (PS _) ts) = concatMap varsInTerm ts
 varsInForm (Not phi) = varsInForm phi
 varsInForm (Disj phi psi) = varsInForm phi ++ varsInForm psi
 varsInForm (Forall _ phi) = varsInForm phi

 -- Variables in a given term
 varsInTerm :: Term -> [VarSymb]
 varsInTerm (T (VS v) ts) = v:concatMap varsInTerm ts
 varsInTerm (T _ ts) = concatMap varsInTerm ts

 -- First argument: the "context" formula in which we apply the second argument
 -- Second argument: t <- x -> u
 -- Result: the context formula and the corresponding substitutions in it
 termToFormGen :: Form -> TermGen -> Gen
 termToFormGen context (vs, t, u) = (context, aux context vs t, aux context vs u) where
   -- First argument: the "context" formula in which we apply the second and third argument
   -- Second argument: x
   -- Third argument: t
   -- Result: the (chain of) substitutions that result in x -> t inside of context
   aux :: Form -> VarSymb -> Term -> [Sub]
   aux phi vs (T (FS fs) ts) = SF (F (newVar, fs)) : termToFormGenRec (newVar:varsInForm phi) vs (T (VS newVar) ts) where
     newVar = newVariable (varsInForm phi)

 termToFormGenRec :: [VarSymb] -> VarSymb -> Term -> [Sub]
 termToFormGenRec vars vs (T (VS vs') (T (FS fs) _:ts)) = SF (F (newVar, fs)) : SI (AI (newVar', vs', newVar, 0)) : termToFormGenRec (newVar':newVar:vars) vs (T (VS vs') ts) where
   newVar = newVariable vars
   newVar' = newVariable (newVar:vars)
 termToFormGenRec _ vs (T (VS vs') []) = [SR (R (vs, vs'))]

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

 --          generalized domain -> analogical pairs (s,t'), where t' is the expanded target domain 
 transfer :: [Gen] -> [(Form, Form)]
 transfer gens = [ (apply' s g, apply' t' g) | (g, s, _) <- gens, (_, _, t') <- gens ]

\end{code}


