\subsection{Examples}

\begin{code}
module GrammarEx where

import Data.List
import Automaton
import Grammar
\end{code}

\begin{example}\label{ex:gex}
\begin{code}
gex1::Grammar
gex1=(['a','b'],['S'],[('S',"aSb"),('S',"")],'S')
gex2::Grammar
gex2=(['a','b'],['S','A'],[('S',"A"),('S',"aSb"),('A',"aA"),('A',"")],'S')
gex3::Grammar
\end{code}

\begin{screen}
\begin{verbatim}
*GrammarExChar> gex1
("ab","S",[('S',"aSb"),('S',"")],'S')
*GrammarExChar> take 10 $ Grammar.language gex1
["","ab","aabb","aaabbb","aaaabbbb","aaaaabbbbb","aaaaaabbbbbb",
 "aaaaaaabbbbbbb","aaaaaaaabbbbbbbb","aaaaaaaaabbbbbbbbb"]
*GrammarExChar> gex2
("ab","SA",[('S',"A"),('S',"aSb"),('A',"aA"),('A',"")],'S')
*GrammarExChar> take 10 $ Grammar.language GrammarEx.gex2
["","a","ab","aa","aab","aabb","aaa","aaab","aaabb","aaabbb"]
\end{verbatim}
\end{screen}
\begin{code}
t002::[SymbolString]
t002=take 10 $ Grammar.language GrammarEx.gex1
t004::[SymbolString]
t004=take 10 $ Grammar.language GrammarEx.gex2
gex3=(['0','1','(',')','+'],['S'],
      [('S',"(S+S)"),('S',"0"),('S',"1")],'S')
t006=take 10 $ Grammar.language GrammarEx.gex3
\end{code}
\end{example}

\begin{code}
flanguage::(SymbolString->Bool)->Grammar->[SymbolString]
flanguage f g@(t,n,rs,s0) = filter (Grammar.terminalQ t) $
                                   (sfstep f (Grammar.onestep' rs)) [[s0]]
\end{code}

\begin{example}
Examples using \verb|flanguage| function.
\begin{screen}
\begin{verbatim}
*GrammarEx> flanguage (\x->((length x)<20)) gex1
["","ab","aabb","aaabbb","aaaabbbb","aaaaabbbbb","aaaaaabbbbbb",
 "aaaaaaabbbbbbb","aaaaaaaabbbbbbbb","aaaaaaaaabbbbbbbbb"]
*GrammarEx> flanguage (\x->((length x)<10)) gex2
["","a","ab","aa","aab","aabb","aaa","aaab","aaabb","aaabbb",
 "aaaa","aaaab","aaaabb","aaaabbb","aaaabbbb","aaaaa","aaaaab",
 "aaaaabb","aaaaabbb","aaaaaa","aaaaaab","aaaaaabb","aaaaaaa",
 "aaaaaaab","aaaaaaaa"]
\end{verbatim}
\end{screen}
\begin{code}
t007=flanguage (\x->((length x)<20)) GrammarEx.gex1
t008=flanguage (\x->((length x)<10)) GrammarEx.gex2
\end{code}
\end{example}

