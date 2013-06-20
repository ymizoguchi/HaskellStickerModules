\subsection{Basic Definitions}

Let $\Sigma$ be an alphabet set.
$\Sigma^*$ is the set of all strings over $\Sigma$ 
including the empty string $\varepsilon$.
For a natural number $n$, $\Sigma^n=\{w \in \Sigma^*| |w|=n\}$
and $\Sigma^{\le n}=\{w \in \Sigma^*| 1 \le |w| \le n\}$.

Haskell function \verb|(sstar s)|
computes the infinite elements set $\Sigma^*$
over \verb|s|$=\Sigma$.
We can also compute $\Sigma^n$ and $\Sigma^{\le n}$
by \verb|(sigman n s)| and \verb|(sigmann n s)|, respectively.

We use types \verb|Symbol| for alphabets,
\verb|SymbolString| for strings, and
\verb|SymbolSet| for sets of alphabets.

\begin{code}
module Automaton where
import Data.List

type Symbol = Char
type SymbolString = [Symbol]
type SymbolSet    = [Symbol]
\end{code}

\begin{code}
sstar :: Eq a => [a] -> [[a]]
sstar [] = []
sstar s  = [[]] ++ (union' [ [[x] ++ w | w <- (sstar s)] | x <- s ])

sigman :: Eq a => [a] -> Int -> [[a]]
sigman s 0 = [[]]
sigman s n = concat' ss (sigman s (n-1))
             where ss = map (\x -> [x]) s

sigmann :: Eq a => [a] -> Int -> [[a]]
sigmann s 0 = []
sigmann s n = (sigmann s (n-1)) ++ (sigman s n)
\end{code}

We call a subset $A$ of $\Sigma^*$ as a language over $\Sigma$.
For a set of languages \verb|u|$=S$, the set $\cup \{x |x \in S\}$
is computed by \verb|(union' u)|.
For languages \verb|x|$=X$, and \verb|y|$=Y$,
the set $X \cdot Y =\{xy|x \in X,\  y \in Y\}$
is computed by \verb|(concat' x y)|.
And the set $X^*=\cup \{X^i | i \in {\bf N}\}$
is computed by \verb|(star x)|.

\begin{code}
union':: Eq a =>[[a]]->[a]
union' [] = []
union' (x:xs) | x == []   = union' xs
             | otherwise = [head x]++(union' (xs++[tail x]))

concat'::Eq a => [[a]]->[[a]]->[[a]]
concat' [] y = []
concat' x [] = []
concat' (xh:xs) (yh:ys) =  [xh++yh] 
   ++ union' [ (concat' [xh] ys), (concat' xs [yh]), (concat' xs ys)]

star :: Eq a => [[a]] -> [[a]]
star [] = []
star s  = [[]] ++ (union' [ [x ++ w | w <- (star s)] | x <- s ])
\end{code}

We note that the functions \verb|union'|, \verb|concat'|, and
\verb|star| are applicable for languages which contains infinite
elements.
Even though the fuction \verb|union| and \verb|concat| in Data.List modules
are not applicable for infinite sets.
\subsection{Automaton}

We use types \verb|State| for states,
\verb|States| for sets of states, and
\verb|Automaton| for automata.

We can naturally extend a state transition function
$\delta:Q  \times \Sigma \to Q$
to $\delta^*: Q \times \Sigma^* \to Q$.
For a fuction \verb|d|$=\delta$,
the function $\delta^*$ is computed by \verb|dstar d|.

\begin{code}
type State = Int
type States = [State]
type Automaton = (States, [Symbol], State->Symbol->State, State, States)

dstar::(State->Symbol->State)->State->SymbolString->State
dstar d s [] = s
dstar d s (a:w) = dstar d (d s a) w
\end{code}

For an automaton \verb|m|$=M=(Q,\Sigma,\delta,q_0,F)$,
an accepted language
$$
L(M)=\{w \in \Sigma^* \, |\, \delta^*(w) \in \, F\}
$$
is computed by \verb|(language m)|.

\begin{code}
accepts::Automaton->[String]->[String]
accepts (q,s,d,s0,f) ss = [w | w <- ss, (dstar d s0 w) `elem` f]

language::Automaton ->[String]
language m@(q,s,d,s0,f) = accepts m (sstar s)
\end{code}

\subsection{Translation}

In this section, we defines meta-functions for transformations.

A function $f:A \to 2^B$ is naturally extended to
a function $\hat{f}:2^A \to 2^B$
by defining $\hat{f}(X)=\cup \{f(x)| x \in X\}$ for $X \subset A$.
The function $\hat{f}$ is computed by  \verb|(power f)|.

\begin{code}
power::(Eq a,Eq b)=>(a->[b])->[a]->[b]
power f ss = union' [(f s)|s<-ss]
\end{code}

For a function $f:A \to 2^A$,
$n$-th repeated function is defined by
$\hat{f}^n(X)=\cup \{f(x)|x \in f^{n-1}(X)\}$,
where $f^0(X)=\phi$.
For a predicate $P:A \to \{true,false\}$,
we define the function
$\hat{f}^n_P(X)=\cup \{f(x)\,|\, (x \in f^{n-1}_P(X)) \, \land \, P(f(x))\, \}$.

$\hat{f}^n$ and $hat{f}^n_P$ are computed by
\verb|(nstep n f)| and \verb|(nfstep p n f)|, respectively.

\begin{code}
nstep::Eq a=>Int->(a->[a])->[a]->[a]
nstep 0 _ _  = []
nstep 1 f ss = (power f) ss
nstep n f ss = (power f) $ nstep (n-1) f ss

nfstep::Eq a=>(a->Bool)->Int->(a->[a])->[a]->[a]
nfstep _ 0 _ _  = []
nfstep p 1 f ss = filter p ((power f) ss)
nfstep p n f ss = filter p $ (power f) $ nfstep p (n-1) f ss
\end{code}

$f^*(X)=\cup \{f^i(X)|i \in {\bf N}\}$ is computed by \verb|(sstep f)|.
$f^*_P(X)=\cup \{f^i_P(X)| i \in {\bf N}\}$ is computed by
\verb|(sfstep p f)|.

\begin{code}
sstep::Eq a=>(a->[a])->[a]->[a]
sstep f s0 = nub $ s0 ++ (g f s0)
      where g f [] = []
            g f ss = nub $ ss ++ (g f ((power f) ss))

sfstep::Eq a=>(a->Bool)->(a->[a])->[a]->[a]
sfstep p f s0 = nub $ s0' ++ (g f s0')
  where s0' = filter p s0
        g f [] = []
        g f ss = nub $ (filter p ss) ++ (g f ((power f) (filter p ss)))
\end{code}

