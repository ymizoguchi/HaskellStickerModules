\subsection{Domino}

Let $\Sigma$ be a set of alphabvet,
$\mathbf{Z}$ a set of integers,
and $\rho\subseteq \Sigma\times \Sigma$�D

\begin{definition}[Domino]
An element $(l,r,x)$ of $\Sigma^* \times \Sigma^* \times \mathbf{Z}$
is a {\bf domino} over $(\Sigma,\rho)$, if following conditions holds:
\begin{itemize}
 \item If $x\geq 0$ then $(l[i+x],r[i])\in \rho,
 1\leq i\leq min(length(r)-x,length(l))$
 \item If $x<0$ then $(l[i],r[i-1])\in \rho,
 1\leq i\leq min(length(r)+x,length(l))$
\end{itemize}
We denote the set of all dominos over $(\Sigma,\rho)$
by $D$.
We define $WK=\{(l,r,0)\in D| |l|=|r|\}$.
\end{definition}

\begin{code}
module Sticker where

import Data.List
import Automaton

type Domino = (SymbolString,SymbolString,Int)
type Rho = [(Symbol,Symbol)]
type Lrset = [(Symbol,Symbol)]
type Sticker = ([Symbol],Rho,[Domino],[(Domino,Domino)])
\end{code}

\verb|(lrcheck rho (l,r,x))| is a function
to chek $(l,r,x)$ is a domino or not.

\begin{code}
lr :: Domino -> Lrset

lr ([],[],x) = []
lr ([],(rh:rt),x) = []
lr ((lh:lt),[],x) = []
lr (l@(lh:lt),r@(rh:rt),x) = if (x > 0) then (lr (lt,r,x-1))
                             else (if (x == 0) then ((lh,rh):(lr (lt,rt,0)))
                                     else (lr (l,rt,x+1)))
lrcheck :: Rho -> Domino -> Bool
lrcheck rho (l,r,x) = ((length lrset1) == (length lrset2))
                    where lrset2 = filter (\x -> (x `elem` rho)) lrset1
                          lrset1 = (lr (l,r,x))
wk :: Domino -> Bool
wk (l,r,x) | x==0 = (length l) == (length r)
           | otherwise = False
\end{code}

\begin{definition}[Sticker Operation]
Sticker operation $\mu:D \times D \rightarrow D \cup \{\bot \}$
is defined as follows:
$$
\mu((l_1,r_1,x_1),(l_2,r_2,x_2)) = \left \{
\begin{array}{l}
(l_1l_2,r_1r_2,x_1) \mbox{\ \ \ (if the condition (*) holds)} \\
\bot                \mbox{\ \ \ (otherwise)}
\end{array}
\right.
$$
(*) $(l_1 l_2,r_1 r_2,x)\in D$ and $x_1+ length(r_1)-length(l_1) = x_2$
\end{definition}


The function \verb|mu| is an implementation
of the sticker operation $\mu$.


\begin{code}
mu :: Rho -> Domino -> Domino -> [Domino]
mu rho (l1,r1,x1) (l2,r2,x2) =
        if (((x1 + (length r1) - (length l1)) == x2) &&
           (lrcheck rho (l1++l2,r1++r2,x1))) then  [(l1++l2,r1++r2,x1)]  
           else []

mu' :: Rho -> (Domino,Domino) -> Domino -> [Domino]
mu' rho (l,r) d = concat $ map (mu rho l) $ mu rho d r
\end{code}

\subsection{Sticker System}

\begin{definition}[Sticker System]
Sticker System  $\gamma$ is four tuple $\gamma=(\Sigma,\rho,A,R)$
of an alphabet set $\Sigma$,
$\rho\subseteq \Sigma\times \Sigma$,
a finite set of axioms $A(\subseteq D)$
and a finite set of dominos $R\subseteq D\times D$.
\end{definition}

For a sticker system $\gamma=(\Sigma,\rho,A,R)$,
we define a relation $\Rightarrow$ as follows.

$$
x\Rightarrow y~~ \stackrel{def}{\Longleftrightarrow}~~ \exists (u,v)\in R,y=\mu(u,\mu(x,v))
$$
Let $\Rightarrow ^*$ be the reflective and transitive coluser of $\Rightarrow$.

The set of dominos $LM(\gamma)$ generated by $\gamma$ is
$$
LM(\gamma)=\{b\in WK | a\Rightarrow ^* b,a\in A\}.
$$

The language $L(\gamma)$ generated by $\gamma$ is
$$
L(\gamma)=\{l\in \Sigma^* | a \Rightarrow (l,r,0) \in WK, \exists r\in \Sigma^* ,\exists a \in A \}.
$$

\begin{code}
onestep :: Rho -> [(Domino,Domino)] -> Domino -> [Domino]
onestep rho rr d = concat $ map (\x->(mu' rho x d)) rr

language::Sticker->[SymbolString]
language stk = map f $ filter wk $ Sticker.generate stk
         where f (x,y,z) = x

generate::Sticker->[Domino]
generate (s,rho,a,r) = (sstep (Sticker.onestep rho r)) a

\end{code}

