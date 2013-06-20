\subsection{Sticker System vs Linear Grammar}
\begin{definition}
For a linear grammar $G=(N,\Sigma,S,P)$,
sticker system  $\gamma_G = (\sigma,\rho,A,R)$ is defined as follows.
\begin{eqnarray*}
\rho &=& \{(a,a)|a\in \Sigma\}\\
X_1 &=& S~~~~~ \mbox{(if $i=1$ then $X_i=S$)}\\
T(i,k) &=& \{w\in T^*|X_i \Rightarrow ^* w,|w|=k \}\\
T(i,l,r)&=& \{(w_l,j,w_r) \in (T^* \times \textrm{\boldmath $N$} \times T^*)|X_i\Rightarrow w_l X_j w_r,|w_l|=l,|w_r|=r\}\\
A &=& A_1\cup A_2 \cup A_3\\
A_1 &=& \{(x,x,0)|x\in T(0,m),m\leq 3k + 1 \}\\
A_2 &=& \{(ux,x,|u|)|w\in T(i,m),1+m \leq m \leq 3k+1 ,\\
    &~& x=Right(w,m-i),u=Left(w,i) \}\\
A_3 &=& \{(xu,x,0)|w\in T(i,m),1+m \leq m \leq 3k+1,\\
    &~& x=Left(w,m-i),u=Right(w,i) \}\\
R &=& R_1\cup R_2 \cup R_3 \cup R_4 \cup R_5 \cup R_6 \\
R_1 &=& \bigcup^k _{i=1} \bigcup^{k+1} _{l=0} \{ ((ux,xv,|u|),(z,z,0))|(w,j,z)\in T(i,k+1,l),\\
    &~& u=Left(w,i),x=Right(w,i),v\in \Sigma^j \}\\
R_2 &=& \bigcup^k _{i=1} \bigcup^{k+1} _{l=0} \{ ((x,xv,0),(zu,z,0))|(x,j,w)\in T(i,l,k+1),\\
    &~& z=Left(w,k+1-i),u=Right(w,i),v\in \Sigma^j \}\\
R_3 &=& \bigcup^{2k+1} _{l=1} \{ ((x,xv,0),(z,z,0))|(x,j,z)\in T(0,l,m),1\\
    &~& 0 \leq m \leq 2k+1-l,v\in \Sigma^j \}\\
R_4 &=& \bigcup^k _{i=1} \bigcup^{k+1} _{l=0} \{ ((z,z,0),(xu,vx,-|v|))|(z,j,w)\in T(i,l,k+1),\\
    &~& x=Left(w,k+1-i),u=Right(w,i),v\in \Sigma^j \}\\
R_5 &=& \bigcup^k _{i=1} \bigcup^{k+1} _{l=0} \{ ((uz,z,|u|),(x,vx,-|v|))|(w,j,z)\in T(i,k+1,l),\\
    &~& u=Left(w,i),x=Right(w,k+1-i),v\in \Sigma^j \}\\
R_6 &=& \bigcup^{2k+1} _{l=1} \{ ((z,z,0),(x,vx,-|v|))|(z,j,x)\in T(0,m,l),\\
    &~& 0\leq m \leq 2k+1-l,v\in \Sigma^j \} \\
k &=& |N|
\end{eqnarray*}
\end{definition}

\begin{theorem}[\cite{paun1998}(Theorem~8)]
$$
L(\gamma_G)=L(G)
$$
\end{theorem}
\hfill$\qed$

\begin{code}
module StickerEx2 where

import Data.List
import Automaton
import Sticker
import Grammar
import GrammarEx

tik::Grammar->Int->Int->[SymbolString]
tik g@(t,n,rs,s0) i k = [w| w<-(fgen m g (n!!(i-1))), (length w)==k]
      where m s = ((length s) <= k+1)

tilr::Grammar->Int->Int->Int->[(SymbolString,Int,SymbolString)]
tilr g@(t,n,rs,s0) i l r = concat [(tilr' g i l r j)|j<-[1..k]]
       where k = length n

tilr'::Grammar->Int->Int->Int->Int->[(SymbolString,Int,SymbolString)]
tilr' g@(t,n,rs,s0) i l r j = [(lpart n w,j,rpart n w)| 
                  w<-(ffgen m g (n!!(i-1)) (n!!(j-1))), 
                  and[((length (lpart n w))==l),(length (rpart n w))==r]]
      where m s = ((length s) <= (l+r+1))

gA::Grammar->[Domino]
gA s = (gA1 s) ++ (gA2 s) ++ (gA3 s)

gA1::Grammar->[Domino]
gA1 s@(t,n,rs,s0) = [(x,x,0)|m<-[1..(3*k+1)],x<-(tik s 1 m)]
          where k = (length n)

gA2'::Int->Grammar->[Domino]
gA2' i s@(t,n,rs,s0) = [(w,(drop i w),i)|m<-[1..(3*k+1)],w<-(tik s i m)]
          where k = length n

gA2::Grammar->[Domino]
gA2 g@(t,n,rs,s0) = concat [(gA2' i g)|i<-[1..(length n)]]

gA3'::Int->Grammar->[Domino]
gA3' i g@(t,n,rs,s0) = [(w,(take (m-i) w),0)|
                             m<-[1..(3*k+1)],w<-(tik g i m)]
          where k  = length n

gA3::Grammar->[Domino]
gA3 g@(t,n,rs,s0) = concat [(gA3' i g)|i<-[1..(length n)]]

gR::Grammar->[(Domino,Domino)]
gR g = concat [gR1 g, gR2 g, gR3 g, gR4 g, gR5 g, gR6 g]

gR1'::Int->Int->Grammar->[(Domino,Domino)]
gR1' i l g@(t,n,rs,s0) = [((w,(drop i w)++v,i),(z,z,0))|
         (w,j,z)<-(tilr g i (k+1) l), v<-(sigman t j)]
         where k = length n

gR1::Grammar->[(Domino,Domino)]
gR1 g@(t,n,rs,s0) = concat [(gR1' i l g)|i<-[1..k],l<-[0..(k+1)]]
          where k = length n

gR2'::Int->Int->Grammar->[(Domino,Domino)]
gR2' i l g@(t,n,rs,s0) = [((x,x++v,0),(w,(take i' w),0))|
          (x,j,w)<-(tilr g i l (k+1)), v<-(sigman t j)]
          where k = length n
                i' = k+1-i

gR2::Grammar->[(Domino,Domino)]
gR2 g@(t,n,rs,s0) = concat [(gR2' i l g)|i<-[1..k],l<-[0..(k+1)]]
          where k = length n

gR3'::Int->Int->Grammar->[(Domino,Domino)]
gR3' l m g@(t,n,rs,s0) = [((x,x++v,0),(z,z,0))|
          (x,j,z)<-(tilr g 1 l m), v<-(sigman t j)]
          where k = length n

gR3::Grammar->[(Domino,Domino)]
gR3 g@(t,n,rs,s0) = concat [(gR3' l m g)|l<-[1..(2*k+1)],m<-[0..(2*k+1-l)]]
          where k = length n

gR4'::Int->Int->Grammar->[(Domino,Domino)]
gR4' i l g@(t,n,rs,s0) = [((z,z,0),(w,v++(take i' w),-j))|
          (z,j,w)<-(tilr g i l (k+1)), v<-(sigman t j)]
          where k = length n
                i' = k+1-i

gR4::Grammar->[(Domino,Domino)]
gR4 g@(t,n,rs,s0) = concat [(gR4' i l g)|i<-[1..k],l<-[0..(k+1)]]
          where k = length n

gR5'::Int->Int->Grammar->[(Domino,Domino)]
gR5' i l g@(t,n,rs,s0) = [((w,(drop i w),i),
                          (x,v++x,-j))|
          (w,j,x)<-(tilr g 1 (k+1) l), v<-(sigman t j)]
          where k = length n

gR5::Grammar->[(Domino,Domino)]
gR5 g@(t,n,rs,s0) = concat [(gR5' i l g)|i<-[1..k],l<-[0..(k+1)]]
          where k = length n

gR6'::Int->Int->Grammar->[(Domino,Domino)]
gR6' l m g@(t,n,rs,s0) = [((z,z,0),(x,v++x,-j))|
          (z,j,x)<-(tilr g 1 m l), v<-(sigman t j)]
          where k = length n

gR6::Grammar->[(Domino,Domino)]
gR6 g@(t,n,rs,s0) = concat [(gR6' l m g)|l<-[1..(2*k+1)],m<-[0..(2*k+1-l)]]
          where k = length n
\end{code}

\begin{code}
gGamma::Grammar->Sticker
gGamma g@(t,n,rs,s0) = (t,rho,(gA g),(gR g))
          where rho = map (\x->(x,x)) t
\end{code}

\begin{example}
The followings are sticker systems
induced by linear grammars defined in Example~\ref{ex:gex}.

\begin{screen}
\begin{verbatim}
*StickerEx2> let (t,n,rs,s)=gex1 in rs
[('S',"aSb"),('S',"")]
*StickerEx2> let (t,n,rs,s)=gex2 in rs
[('S',"A"),('S',"aSb"),('A',"aA"),('A',"")]
*StickerEx2> gA gex1
[("ab","ab",0),("aabb","aabb",0),("ab","b",1),("aabb","abb",1),
 ("ab","a",0),("aabb","aab",0)]
*StickerEx2>  gGamma gex1
("ab",[('a','a'),('b','b')],[("ab","ab",0),("aabb","aabb",0),
 ("ab","b",1),("aabb","abb",1),("ab","a",0),("aabb","aab",0)],
 [(("aa","aa",1),("bb","bb",0)),(("aa","ab",1),("bb","bb",0)),
 (("aa","aaa",0),("bb","b",0)),(("aa","aab",0),("bb","b",0)),
 (("a","aa",0),("b","b",0)),(("a","ab",0),("b","b",0)),
 (("aa","aa",0),("bb","ab",-1)),(("aa","aa",0),("bb","bb",-1)),
 (("aa","a",1),("bb","abb",-1)),(("aa","a",1),("bb","bbb",-1)),
 (("a","a",0),("b","ab",-1)),(("a","a",0),("b","bb",-1))])
*StickerEx2> take 10 $ Sticker.language $ gGamma gex1
["ab","aabb","aaabbb","aaaabbbb","aaaaabbbbb","aaaaaabbbbbb",
 "aaaaaaabbbbbbb","aaaaaaaabbbbbbbb","aaaaaaaaabbbbbbbbb",
 "aaaaaaaaaabbbbbbbbbb"]
*StickerEx2> take 20 $ Sticker.language $ gGamma gex2
["a","ab","aa","aab","aaa","aabb","aaab","aaaa","aaabb","aaaab",
 "aaaaa","aaabbb","aaaabb","aaaaab","aaaaaa","aaaabbb","aaaaabb",
 "aaaaaab","aaaaaaa","aaaabbbb"]
*StickerEx2> take 10 $ Sticker.generate $ gGamma gex1
[("ab","ab",0),("aabb","aabb",0),("ab","b",1),("aabb","abb",1),
 ("ab","a",0),("aabb","aab",0),("aaabbb","aabbb",1),
 ("aaaabbbb","aaabbbb",1),("aaabbb","aaabb",0),
 ("aaaabbbb","aaaabbb",0)]
\end{verbatim}
\end{screen}
\begin{code}
gex1rs = let (t,n,rs,s)=gex1 in rs
gex2rs = let (t,n,rs,s)=gex2 in rs
t101 = gA gex1
t102 = gGamma gex1
t103 = take 10 $ Sticker.language $ gGamma gex1
t104 = take 20 $ Sticker.language $ gGamma gex2
t105 = take 10 $ Sticker.generate $ gGamma gex1
\end{code}

\end{example}

