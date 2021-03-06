
\subsection{Code}

\begin{code}
module OutputEx where

import Data.List
import Automaton
import AutomatonEx
import Sticker
import StickerEx1
import Grammar
import GrammarEx
import StickerEx2
import System

st2file::Sticker->String->IO ()
st2file st file = writeFile file $ unlines $ st2tex st

r2file::[(Domino,Domino)]->String->IO ()
r2file rs file = writeFile file $ unlines $ concat $ map r2tex rs

a2file::[Domino]->String->IO ()
a2file rs file = writeFile file $ unlines $ concat $ map d2tex rs

d2s::Domino->Domino
d2s (x,y,k) | (lx < ly) = ((spapnd (ly-lx) ' ' x'), y', 0)
            | otherwise = (x', (spapnd (lx-ly) ' ' y'), 0)
             where lx = length x'
                   ly = length y'
                   (x',y') = f (x,y,k)
                   f (x,y,n) | (n < 0)   = ((spinst (-n) ' ' x),y)
                             | otherwise = (x, (spinst n ' ' y))

spinst::Eq a=>Int->a->[a]->[a]
spinst 0 c l = l 
spinst k c l | (k <= 0) = l
             | otherwise = (c:(spinst (k-1) c l))

sps::Eq a=>Int->a->[a]
sps k c | (k <= 0)  = []
        | otherwise = (c:(sps (k-1) c))

spapnd::Eq a=>Int->a->[a]->[a]
spapnd k c [] = sps k c
spapnd k c (h:t) = (h:(spapnd k c t))

s2tex::(Show a)=>[a]->String
s2tex []    = ""
s2tex (h:t) = (show h)++" & "++(s2tex t)

i2tex::[Char]->String
i2tex [] = ""
i2tex (h:t) | (h == ' ')  = "\\ "++(i2tex t)
            | otherwise = (h:(i2tex t))

d2tex::Domino->[String]
d2tex ([],[],_) = ["\\begin{tabular}{|l|} \\hline",
                   "\\ \\\\ \\ \\\\ \\hline",
                   "\\end{tabular} "]
d2tex d = ["\\begin{tabular}{|l|} \\hline",
           (i2tex x)++" \\\\", (i2tex y)++" \\\\",
                   "\\hline","\\end{tabular} "]
          where (x,y,k) = d2s d

r2tex::(Domino,Domino)->[String]
r2tex (dx,dy) = [ " ( "]++(d2tex dx)
                  ++[" , "]++(d2tex dy)++[") "]

st2tex::Sticker->[String]
st2tex (s,rho,a,d) = [ "\\begin{description}",
                       "\\item[A] "       ]
                     ++  concat (map d2tex a)
                     ++ [ "\\item[R] "    ]
                     ++  concat (map r2tex d)
                     ++ [ "\\end{description}",""]
\end{code}

\begin{example}
The followings are command lists to make prety printed domino output files
using in this article.
\begin{code}
t301=st2file (gGamma gex1) "gex1.tex"
t302=st2file (gGamma gex2) "gex2.tex"
t303=a2file (gA1 gex1) "gex1a1.tex"
t304=a2file (gA2 gex1) "gex1a2.tex"
t305=a2file (gA3 gex1) "gex1a3.tex"
t306=r2file (gR1 gex1) "gex1r1.tex"
t307=r2file (gR2 gex1) "gex1r2.tex"
t308=r2file (gR3 gex1) "gex1r3.tex"
t309=r2file (gR4 gex1) "gex1r4.tex"
t310=r2file (gR5 gex1) "gex1r5.tex"
t311=r2file (gR6 gex1) "gex1r6.tex"
t312=a2file (gA1 gex2) "gex2a1.tex"
t313=a2file (gA2 gex2) "gex2a2.tex"
t314=a2file (gA3 gex2) "gex2a3.tex"
t315=r2file (gR1 gex2) "gex2r1.tex"
t316=r2file (gR2 gex2) "gex2r2.tex"
t317=r2file (gR3 gex2) "gex2r3.tex"
t318=r2file (gR4 gex2) "gex2r4.tex"
t319=r2file (gR5 gex2) "gex2r5.tex"
t320=r2file (gR6 gex2) "gex2r6.tex"
t321=a2file (aA1 mp) "mpa1.tex"
t322=a2file (aA2 mp) "mpa2.tex"
t323=a2file (dD mp)  "mpd.tex"
t324=a2file (dF mp)  "mpf.tex"
\end{code}

\subsection{Examples}

\begin{example}
For an automaton
$M_p=(\{0,1\},\Sigma,\delta,0,\{1\})$ in Example~\ref{ex:mp},
we have the sticker system $gamma_{M_p}=(\Sigma,\rho,A,R)$.
\begin{eqnarray*}
\gamma_{G_1} &=& (\Sigma,\rho,A,R)\\
\rho &=& \{(a,a),(b,b)\}\\
A &=& A_1\cup A_2 
\end{eqnarray*}
{\small\tt
\begin{description}
\item[(A1)]
\input{Examples/mpa1.tex}
\item[(A2)]
\input{Examples/mpa2.tex}
\end{description}
}

\begin{eqnarray*}
R &=& D \cup F
\end{eqnarray*}
{\small\tt
\begin{description}
\item[(D)]
\input{Examples/mpd.tex}
\item[(F)]
\input{Examples/mpf.tex}
\end{description}
}
\end{example}

\begin{example}\label{ex:glin1-2}
For a linear grammar
$G_1=\{ \{S\},\{a,b \},S,\{S\rightarrow \epsilon ,S \rightarrow  aS b \} \}$,
we have the sticker system $\gamma_{G_1}=(\Sigma,\rho,A,R)$.
\end{example}

\begin{eqnarray*}
\gamma_{G_1} &=& (\Sigma,\rho,A,R)\\
\rho &=& \{(a,a),(b,b)\}\\
A &=& A_1\cup A_2 \cup A_3
\end{eqnarray*}

{\small\tt
\begin{description}
\item[(A1)]
\input{Examples/gex1a1.tex}
\item[(A2)]
\input{Examples/gex1a2.tex}
\item[(A3)]
\input{Examples/gex1a3.tex}
\end{description}
}

\begin{eqnarray*}
R &=& R_1\cup R_2 \cup R_3 \cup R_4\cup R_5\cup R_6
\end{eqnarray*}

{\small\tt
\begin{description}
\item[(R1)]
\input{Examples/gex1r1.tex}
\item[(R2)]
\input{Examples/gex1r2.tex}
\item[(R3)]
\input{Examples/gex1r3.tex}
\item[(R4)]
\input{Examples/gex1r4.tex}
\item[(R5)]
\input{Examples/gex1r5.tex}
\item[(R6)]
\input{Examples/gex1r6.tex}
\end{description}
}

\begin{example}
For a linear grammar $G_2=\{ \{S,A \},\{a,b \},S,\{S \rightarrow  aSb,
S \rightarrow A,
A \rightarrow \epsilon,
A \rightarrow aA \} \}$,
we have the sticker system $\gamma_{G_2}=(\Sigma,\rho,A,R)$.
\end{example}

\begin{eqnarray*}
\gamma_{G_2} &=& (\Sigma,\rho,A,R)\\
\rho &=& \{(1,1),(2,2)\}\\
A &=& A_1\cup A_2 \cup A_3
\end{eqnarray*}
{\small\tt
\begin{description}
\item[(A1)]
\input{Examples/gex2a1.tex}
\item[(A2)]
\input{Examples/gex2a2.tex}
\item[(A3)]
\input{Examples/gex2a3.tex}
\end{description}
}
\begin{eqnarray*}
R &=& R_1\cup R_2 \cup R_3 \cup R_4\cup R_5\cup R_6
\end{eqnarray*}
{\small\tt
\begin{description}
\item[(R1)]
\input{Examples/gex2r1.tex}
\item[(R2)]
\input{Examples/gex2r2.tex}
\item[(R3)]
\input{Examples/gex2r3.tex}
\item[(R4)]
\input{Examples/gex2r4.tex}
\item[(R5)]
\input{Examples/gex2r5.tex}
\item[(R6)]
\input{Examples/gex2r6.tex}
\end{description}
}

\end{example}
