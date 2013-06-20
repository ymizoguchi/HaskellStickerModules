\subsection{Sticker System vs Automaton}
\begin{definition}
For a finite automaton $M=(Q,\Sigma,\delta,q_0,F_M)$,
the sticker sytem $\gamma_M=(\Sigma,\rho,A,R)$ is defined as follows.
\begin{eqnarray*}
\rho &=& \{(a,a)|a\in \Sigma \}\\
A &=& A_1\cup A_2\\
A_1 &=& \{(x,x,0)|x\in L(M),|x|\leq k+2 \}\\
A_2 &=& \bigcup_{i=1}^{k+1} \{(xu,x,0)|x\in \Sigma^{\le (k+2-i)},u\in \Sigma^i,\delta^*(0,xu)=i-1 \} \\
R &=& D\cup F  \\
D &=& \bigcup_{i=1}^{k+1} \bigcup_{j=1}^{k+1} \{((\lambda,\lambda,0),(xu,vx,-|v|))|x\in \Sigma^{\le (k+2-i)}, u\in \Sigma^i, v \in \Sigma^j\\
    &&\delta^*(j-1,xu)=i-1 \}\\
F &=& \bigcup_{i=1}^{k+1} \bigcup_{j=1}^{k+1} \{((\lambda,\lambda,0),(x,vx,-|v|))|v\in \Sigma^j, x\in \Sigma^i, \\
    &&\delta(j-1,x)\in F_M \} \\
k &=& |Q| -1 
\end{eqnarray*}
\end{definition}

\begin{theorem}[\cite{paun1998}(Theorem~7)]
$$
L(\gamma_M) = L(M)
$$
\end{theorem}
\hfill$\qed$

\begin{code}
module StickerEx1 where

import Data.List
import Automaton
import Sticker
import AutomatonEx

aA::Automaton->[Domino]
aA m = (aA1 m)++(aA2 m)

aA1::Automaton->[Domino]
aA1 m@(q,s,d,q0,f) = [(x,x,0)|x<-(accepts m (sigmann s (k+2)))]
                     where k = (length q)-1

aA2::Automaton->[Domino]
aA2 m@(q,s,d,q0,f) = concat [(aA2' m i)| i<- [1..(k+1)]]
                     where k = (length q)-1

aA2'::Automaton->Int->[Domino]
aA2' m@(q,s,d,q0,f) i =  [(x++u,x,0)| 
                          (x,u) <- xupair, (dstar d 0 (x++u)) ==(i-1)]
       where xupair = [(x,u)|x<-(sigmann s (k+2-i)), u<-(sigman s i)]
             k = (length q)-1
\end{code}


\begin{code}
dD::Automaton->[Domino]
dD m@(q,s,d,q0,f) = concat [(dD' m (i,j))|i<-[1..(k+1)],j<-[1..(k+1)]]
                    where k = (length q)-1

dD'::Automaton->(Int,Int)->[Domino]
dD' m@(q,s,d,q0,f) (i,j) = concat [
            [(x++u,v++x,-(length v))| 
                x<-(sigmann s ((k+2)-i)), (dstar d (j-1) (x++u))==(i-1)]|
                                    u<- (sigman s i), v<-(sigman s j)]
                    where k = (length q)-1
\end{code}

\begin{code}
dF::Automaton->[Domino]
dF m@(q,s,d,q0,f) = concat $ map (dF' m) [(i,j)|i<-[1..(k+2)],j<-[1..(k+1)]]
      where k = (length q)-1

dF'::Automaton->(Int,Int)->[Domino]
dF' m@(q,s,d,q0,f) (i,j)=
     concat [ 
       [(x,v++x,-(length v))| x<-(sigman s i),
                              (dstar d ((length v)-1) x) `elem` f
             ]| v<-(sigman s j)]
     where k = (length q)-1
\end{code}

\begin{code}
mGamma::Automaton->Sticker
mGamma m@(q,s,d,q0,f) = (s,rho,(aA m),dd)
        where dd = map (\x -> (("","",0),x)) ((dD m)++(dF m))
              rho = map (\x -> (x,x)) s
\end{code}

\begin{example}
The followings are sticker systems
induced by finite automata defined in Example~\ref{ex:mp}.
\begin{screen}
\small
\begin{verbatim}
*Sticker> let (s,rho,a,r)=mGamma mp in (map snd r)
[("aaa","aaa",-1),("bba","abb",-1),("abb","aab",-1),("bab","aba",-1),
("aaa","baa",-1),("bba","bbb",-1),("abb","bab",-1),("bab","bba",-1),
("aba","aaab",-2),("baa","aaba",-2),("aab","aaaa",-2),
("bbb","aabb",-2),("aba","abab",-2),("baa","abba",-2),
("aab","abaa",-2),("bbb","abbb",-2),("aba","baab",-2),
("baa","baba",-2),("aab","baaa",-2),("bbb","babb",-2),
("aba","bbab",-2),("baa","bbba",-2),("aab","bbaa",-2),
("bbb","bbbb",-2),("baa","ab",-1),("aab","aa",-1),("aba","aa",-1),
("bbb","ab",-1),("baa","bb",-1),("aab","ba",-1),("aba","ba",-1),
("bbb","bb",-1),("aaa","aaa",-2),("bab","aab",-2),("bba","aab",-2),
("abb","aaa",-2),("aaa","aba",-2),("bab","abb",-2),("bba","abb",-2),
("abb","aba",-2),("aaa","baa",-2),("bab","bab",-2),("bba","bab",-2),
("abb","baa",-2),("aaa","bba",-2),("bab","bbb",-2),("bba","bbb",-2),
("abb","bba",-2),("b","ab",-1),("b","bb",-1),("a","aaa",-2),
("a","aba",-2),("a","baa",-2),("a","bba",-2),("ab","aab",-1),
("ba","aba",-1),("ab","bab",-1),("ba","bba",-1),("aa","aaaa",-2),
("bb","aabb",-2),("aa","abaa",-2),("bb","abbb",-2),("aa","baaa",-2),
("bb","babb",-2),("aa","bbaa",-2),("bb","bbbb",-2),("aab","aaab",-1),
("baa","abaa",-1),("aba","aaba",-1),("bbb","abbb",-1),
("aab","baab",-1),("baa","bbaa",-1),("aba","baba",-1),
("bbb","bbbb",-1),("aaa","aaaaa",-2),("bab","aabab",-2),
("bba","aabba",-2),("abb","aaabb",-2),("aaa","abaaa",-2),
("bab","abbab",-2),("bba","abbba",-2),("abb","ababb",-2),
("aaa","baaaa",-2),("bab","babab",-2),("bba","babba",-2),
("abb","baabb",-2),("aaa","bbaaa",-2),("bab","bbbab",-2),
("bba","bbbba",-2),("abb","bbabb",-2)]
*Sticker> let (s,rho,a,r)=mGamma mp in a
[("aab","aab",0),("baa","baa",0),("aba","aba",0),("bbb","bbb",0),
("aaa","aa",0),("abb","ab",0),("bba","bb",0),("bab","ba",0),
("baa","b",0),("aab","a",0),("aba","a",0),("bbb","b",0)]
*Sticker> let (s,rho,a,r)=mGamma mp in rh
[('a','a'),('b','b')]
*StickerEx1> take 30 $ Sticker.language $ mGamma mp
["b","ab","ba","aab","baa","aba","bbb","aaab","abbb","babb",
 "bbab","aaba","abaa","baaa","bbba","aaaab","abbab","babab",
 "bbaab","aabaa","abaaa","baaaa","bbbaa","aaaba","abbba",
 "babba","bbaba","aabbb","ababb","baabb"]
\end{verbatim}
\end{screen}
\begin{screen}
\small
\begin{verbatim}
*StickerEx1> let (s,rho,a,r)=mGamma m1 in a
[("a","a",0),("aba","aba",0),("abab","aba",0),("aaaa","a",0),
("aaab","a",0),("abaa","a",0),("bbab","b",0),("aaba","a",0),
("abba","a",0),("aabb","a",0),("abbb","a",0),("baaa","b",0),
("baab","b",0),("bbaa","b",0),("baba","b",0),("bbba","b",0),
("babb","b",0),("bbbb","b",0)]
*StickerEx1> take 4 $ Sticker.language $ mGamma m1
["a","aba","ababa","abababa"]
\end{verbatim}
\end{screen}
\begin{code}
mprr = let (s,rho,a,r)=mGamma mp in (map snd r)
mpa = let (s,rho,a,r)=mGamma mp in a
mprho = let (s,rho,a,r)=mGamma mp in rho
mplanguage = take 30 $ Sticker.language $ mGamma mp
m1rr = let (s,rho,a,r)=mGamma m1 in (map snd r)
m1a = let (s,rho,a,r)=mGamma m1 in a
m1rho = let (s,rho,a,r)=mGamma m1 in rho
m1language = take 4 $ Sticker.language $ mGamma m1
\end{code}

\end{example}

