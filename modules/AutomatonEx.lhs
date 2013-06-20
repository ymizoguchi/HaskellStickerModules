\subsection{Examples}

\begin{code}
module AutomatonEx where
import Data.List
import Automaton
\end{code}

\begin{example}\label{ex:mp}

$L(M_p)=\{w \in \Sigma^* \, |\, |w|_b \mbox{\ \bf mod \ } 2 = 1 \, \}$,
$L(M_1)=\{a(ba)^n | n=0,1,\cdots \}$. 

\begin{code}
mp::Automaton
mp = ([0,1], ['a','b'], dp, 0, [1])
    where dp 0 'a' = 0
          dp 0 'b' = 1
          dp 1 'a' = 1
          dp 1 'b' = 0

m1::Automaton
m1 = ([0,1,2], ['a','b'], d, 0, [1])
     where d 0 'a' = 1
           d 0 'b' = 2
           d 1 'a' = 2
           d 1 'b' = 0
           d 2 'a' = 2
           d 2 'b' = 2
\end{code}
\begin{center}
\begin{tabular}{p{5.5cm}p{5.5cm}}
$M_p$ & $M_1$ \\
\includegraphics[scale=0.6]{fig/figmp.pdf} &
\includegraphics[scale=0.6]{fig/figm1.pdf} 
\end{tabular}
\end{center}

\begin{screen}
\begin{verbatim}
*AutomatonEx> take 10 $ Automaton.language mp
["b","ba","ab","baa","aba","aab","bbb","baaa","abaa","aaba"]
*AutomatonEx> take 5 $ Automaton.language m1
["a","aba","ababa","abababa","ababababa"]
\end{verbatim}
\end{screen}

\begin{code}
t001 = take 10 $ Automaton.language mp
t002 = take 5 $ Automaton.language m1
\end{code}

\end{example}
