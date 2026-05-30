# On the Groups $H(\Pi,n)$, II: Methods of Computation

Samuel Eilenberg and Saunders Mac Lane  
*Annals of Mathematics*, Vol. 70, No. 1, July 1954, pp. 49–139  
Received August 24, 1953

## 1. Introduction

The homology ring $H(\Pi,n)$ is defined, for any abelian group $\Pi$ and any positive integer $n$, as the homology ring of the complex $K(\Pi,n)$. The main result of the first paper of this series[^1] was the replacement of the complex $K(\Pi,n)$ by an equivalent complex $A(\Pi,n)$. The present investigation[^2] uses the perspicuous algebraic structure of this complex $A(\Pi,n)$ to set up methods for the invariant computation of some of the integral homology groups $H_{n+k}(\Pi,n)$. This program is carried out in detail for $k\leq 5$ and $n=2$, except for $H_6(\Pi,2)$. Invariant cohomology results for the groups $H^{n+k}(\Pi,n;G)$ are also obtained for $k\leq n$, $k=2,3,4$, and $5$.

To illustrate our methods, we cite the isomorphism

$$(1.1)\qquad \theta:\Pi/2\Pi+\Pi/3\Pi\cong H_6(\Pi,5),$$

obtained by assigning to the cosets $x+2\Pi$ and $y+3\Pi$ the homology classes of the cycles given in the complex $A(\Pi,5)$ by the single cells denoted as $[x\mid x]$ and $[y\mid y\mid y]$, respectively. The simplicity of this result is due to the fact that the homology group $H_6(\Pi,5)$ is stable under suspension. Our main interest lies in a treatment which also includes the intrinsically more involved unstable cases. In these cases, simple functors like $\Pi/2\Pi$ and $\Pi/3\Pi$ do not suffice. We are therefore forced to treat a number of new and sometimes quite bizarre functors of $\Pi$.

Once the natural homomorphism $\theta$ above has been formulated for an arbitrary abelian group $\Pi$, the subsequent proof that it is an isomorphism can be restricted to finitely generated groups and thus to direct sums of cyclic groups.

For direct sums our first concern is the establishment of a chain equivalence

$$(1.2)\qquad A(\Pi_1+\Pi_2,n)\simeq A(\Pi_1,n)\otimes A(\Pi_2,n).$$

Geometrically, this can be achieved rapidly by consideration of the cartesian product $X_1\times X_2$ of two spaces $X_1$ and $X_2$ whose only nontrivial homotopy groups are $\pi_n(X_1)=\Pi_1$ and $\pi_n(X_2)=\Pi_2$. However, our subsequent use of the equivalence (1.2) requires that the chain mappings in both directions be explicit and natural. This need is met by the analysis of Chapter I. We begin by setting up an explicit equivalence for the Eilenberg-Zilber theorem $K_1\times K_2\simeq K_1\otimes K_2$ on $FD$-complexes $K_1$ and $K_2$ [8]. This leads up to the corresponding “tensor product theorem”

$$(1.3)\qquad B(G_1\otimes G_2)\simeq B(G_1)\otimes B(G_2)$$

for the bar construction on graded boundary rings $G_1$ and $G_2$. Since the complex $A(\Pi,n)$ is obtained by $n$-fold application of this bar construction to the integral group ring of $\Pi$, the direct sum theorem (1.2) is then obtained.

The direct sum theorem shows that the functor $H_q(\Pi,n)$ is additive in the stable cases $(q<2n)$; in particular

$$(1.4)\qquad H_6(\Pi_1+\Pi_2,5)\cong H_6(\Pi_1,5)+H_6(\Pi_2,5).$$

This reduces the verification that $\theta$ is an isomorphism in (1.1) to the case of cyclic groups. This reduction is no longer possible for homology groups which are not stable; for instance, in the immediately preceding case the isomorphism (1.4) is replaced by

$$H_5(\Pi_1+\Pi_2,4)\cong H_5(\Pi_1,4)+H_5(\Pi_2,4)+\Pi_1\otimes\Pi_2.$$

The extra term $\Pi_1\otimes\Pi_2$ present here is called the “cross-effect” for the functor $H_5(\Pi,4)$. Chapter II studies such cross-effects for an arbitrary covariant functor $T(\Pi)$, including the higher cross-effects which arise when the initial cross-effect is not additive in its arguments $\Pi_1$ and $\Pi_2$. This theory of cross-effects is of independent interest, and our exposition of it is self-contained. With the direct sum theorem and the analysis of cross-effects, the verification in unstable cases that maps like $\theta$ are isomorphisms is reduced to the cases of cyclic groups and of cross-effects of several cyclic groups.

For a cyclic group $Z_h$ of order $h$, Chapter III shows that the complex $A(Z_h,n)$ may be replaced by a much simpler complex $M(h,n)$ which is finite in each dimension. This guarantees the computability of the groups $H_q(\Pi,n)$ and their cross-effects in the category of all finitely generated abelian groups $\Pi$ and of all homomorphisms of one such group into another.

Using the methods thus built up, Chapter IV derives the invariant results promised at the start of our introduction.

The following incidental results may be noted:

Since the well-known Künneth relations play an important part in our discussion of cross-effects on $H_q(\Pi,n)$, we find it necessary and useful to give a brief proof of these relations in §12. This is based on a discussion of cross-caps and a novel definition (§11), using generators and relations, of the torsion product of abelian groups.

The analysis of certain cycles present in $A(\Pi,n)$ suggests the introduction of two rings $\Gamma(\Pi)$ and $\Lambda(\Pi)$, (§§18, 19), defined for any abelian group $\Pi$. They are analogous to the polynomial algebra and the exterior algebra defined for a vector space.

As a by-product of the discussion of the cohomology group $H^4(\Pi,2;G)$ we obtain a rapid proof (Theorem 26.2) of a theorem due to N. J. S. Hughes [12], which in turn is connected with certain results on symmetric cohomology groups of $A(\Pi,1)$. In this connection we also derive the useful isomorphism

$$\operatorname{Ext}_{\mathrm{abel}}(\Pi/p\Pi,G)\cong \operatorname{Hom}(\Pi,G/pG),$$

valid for any prime $p$ (Theorem 26.5).

## Chapter I. Tensor and Cartesian Products of Complexes

## 2. The Eilenberg-Zilber theorem

The bar construction was defined in I in stages, using $FD$-complexes and then $R$-complexes. The tensor product theorem (1.3) will be obtained in parallel stages and finally in an iterated form (§5). The transfer of cup products under the main map $k_n:A(\Pi,n)\to K(\Pi,n)$ is treated in §7.

For $FD$-complexes, the product $\nabla$ defined in I, §5 yields a chain transformation

$$(2.1)\qquad \nabla:K\otimes L\longrightarrow K\times L$$

defined by the formula

$$(2.2)\qquad \nabla(a\otimes b)=a\nabla b,\qquad a\in K,\ b\in L.$$

**Theorem 2.1.** *If $K$ and $L$ are $FD$-complexes, then the map $\nabla$ and the map $f$ defined in (2.9) below provide a chain equivalence*

$$K\times L\ \underset{\nabla}{\overset{f}{\rightleftarrows}}\ K\otimes L.$$

The statement that the pair $f,\nabla$ is a chain equivalence means, as usual, that each of the composites $f\nabla$ and $\nabla f$ is chain homotopic to the appropriate identity map.

Each complex $K,L$, and $K\times L$ determines a normalized complex $K_N,L_N$ and $K\times_N L=(K\times L)_N$; furthermore the product $K_N\otimes L_N$ may be regarded as the quotient of $K\otimes L$ by the subcomplex spanned by all norms $a\otimes Db$ and $Da\otimes b$, for $a\in K$, $b\in L$. The analogue of Theorem 2.1 for these normalized complexes is

**Theorem 2.1a.** *If $K$ and $L$ are $FD$-complexes, then the maps $f$ and $\nabla$ above induce a chain equivalence*

$$K\times_N L\ \underset{\nabla}{\overset{f}{\rightleftarrows}}\ K_N\otimes L_N;$$

*explicitly, there is a homotopy $\Phi$ in $K\times_N L$, and*

$$(2.3)\qquad f\nabla=i,\qquad \partial\Phi+\Phi\partial=\nabla f-i,$$

*where each $i$ denotes the appropriate identity map. The homotopy $\Phi$ has the following annihilation properties (modulo norms):*

$$(2.4)\qquad \Phi\nabla=0,\qquad f\Phi=0.$$

*The maps $f$ and $\nabla$ and the homotopy $\Phi$ are natural.*

**Proof.** In view of the normalization Theorem I.4.1, it suffices to prove the second version of the theorem. The fact that $\nabla$ induces a chain transformation for the normalized complexes was already established in Lemma I.5.3. We shall define $f$ and $\Phi$ on the original (unnormalized) complexes, verify that they map norms into norms, and show that (2.3) and (2.4) hold modulo norms.

In any $FD$-complex $K$, denote the “last” face operator by $F$; thus if $a\in K_q$, then $Fa=F_q a$. The powers of the first and last face operators are then

$$(2.5)\qquad F_0^{\,i}a_q=F_0F_1\cdots F_{i-1}a_q,\qquad F^{\,i}a_q=F_{q-i+1}\cdots F_q a_q,\qquad 0\leq i\leq q.$$

Note the following consequences of the basic $FD$-commutation rules of I, §2, for $b_{q-1}\in K_{q-1}$:

$$(2.6)\qquad
F_0^{\,i}D_jb_{q-1}=D_{j-i}F_0^{\,i}b_{q-1},\qquad 0\leq i\leq j\leq q-1,$$

$$F_0^{\,i}D_jb_{q-1}=F_0^{\,i-1}b_{q-1},\qquad 0\leq j<i\leq q,$$

and

$$(2.7)\qquad
F^{\,i}D_jb_{q-1}=F^{\,i-1}b_{q-1},\qquad 0\leq i\leq j\leq q-1,$$

$$F^{\,i}D_jb_{q-1}=D_jF^{\,i}b_{q-1},\qquad 0\leq j<i\leq q.$$

Now define $f_i:K_q\times L_q\to K_i\otimes L_{q-i}$ by

$$(2.8)\qquad f_i(a_q\times b_q)=F^{\,q-i}a_q\otimes F_0^{\,i}b_q,
\qquad 0\leq i\leq q,$$

and set $f=f_0+\cdots+f_q$, so that

$$(2.9)\qquad f(a_q\times b_q)=\sum_{i=0}^q F^{\,q-i}a_q\otimes F_0^{\,i}b_q,\qquad a_q\in K_q,\ b_q\in L_q.$$

The proof that $f:K\times L\to K\otimes L$ is a chain transformation is straightforward and will be omitted; it is substantially identical with the familiar proof of the boundary formula for the Alexander-Whitney cup product in a simplicial complex.

To show that $f$ maps norms into norms, compute, for $0\leq j\leq q-1$,

$$f_iD_j(a_{q-1}\times b_{q-1})=f_i(D_ja_{q-1}\times D_jb_{q-1})=F^{\,q-i}D_ja_{q-1}\otimes F_0^{\,i}D_jb_{q-1}.$$

For $i\leq j$, the second factor is a norm by (2.6), while, for $i>j$, the first factor is a norm by (2.7).

To show that $f\nabla(a_p\otimes b_q)=a_p\otimes b_q$, modulo norms, compound $f_i$ with the explicit formula (I.5.3) for $\nabla$. The result is a sum of terms $T$ of the form

$$T=\varphi(\varepsilon(\mu))\,F^{\,p-i}D_{\mu_1}\cdots D_{\mu_i}a_p\otimes F_0^{\,i}D_{\nu_{i+1}}\cdots D_{\nu_q}b_q,
\qquad \varphi(\varepsilon)=(-1)^t,$$

with $0\leq i\leq p+q$ and $(\mu,\nu)$ a $(p,q)$-shuffle. Now apply the rules (2.6) and (2.7) to move the powers of $F_0$ and $F$ past the $D$’s. If $i<p$, the second factor of $T$ will then have at least one $D$ in front, and $T$ is thus a norm. If $i>p$, the first factor has fewer $F$’s than $D$’s, hence will have at least one $D$ in front, so that $T$ is again a norm. If $i=p$, (2.6) shows that the second factor has a $D$ in front except in the case when $\mu_p=p-1,\ldots,\mu_1=0$, in which event the second factor of $T$ is exactly $b_q$. In this one case $\nu_q=p+q-1,\ldots,\nu_1=p$, and (2.7) shows that the first factor of $T$ is exactly $a_p$. Furthermore the sign $\varphi(\varepsilon(\mu))$ is positive in this case, so that this one term yields $a_p\otimes b_q$, as desired.

The notions of derived $FD$-operators, as developed in I, §3, may be applied in the present context. Thus any natural homomorphism

$$M=M_{K,L}:K_p\otimes L_s\longrightarrow K_q\otimes L_r,$$

as in Theorem I.3.1, can be written uniquely in the form

$$(2.10)\qquad M(a_p\otimes b_s)=\sum_i m_i\bigl(\beta_i^*a_p\otimes\gamma_i^*b_s\bigr),$$

with integral coefficients $m_i$ and monotonic maps $\beta_i:[p]\to[q]$ and $\gamma_i:[r]\to[s]$. The derived operator $M':K_{p+1}\otimes L_{s+1}\to K_{q+1}\otimes L_{r+1}$ is then defined by

$$M'(a_{p+1}\otimes b_{s+1})=\sum_i m_i\bigl((\delta^0\beta_i)^*a_{p+1}\otimes(\delta^0\gamma_i)^*b_{s+1}\bigr).$$

The operator $M$ is frontal if each $\beta_i$ and $\gamma_i$ involved is frontal, and Lemma I.3.3 applies to such operators on $K_q\times L_q\to K_r\times L_r$.

Now consider the composite chain transformation $h=\nabla f:K\times L\to K\times L$, and note that

$$(2.11)\qquad h(a_0\times b_0)=a_0\times b_0,$$

$$h(a_1\times b_1)=D_0F_1a_1\times b_1+a_1\times D_0F_0b_1.$$

The derived operator $h':(K\times L)_p\to(K\times L)_p$ is then defined for $p>0$, and satisfies $\partial^*h'=h'\partial^*$ and $F_0h'=hF_0$. Since $f$ and $\nabla$ separately map norms into norms, so does $h$; in other words

$$hD_i(a_{q-1}\times b_{q-1})\in D(K\times L),\qquad 0\leq i\leq q-1.$$

Therefore

$$(2.12)\qquad h'D_i(a_q\times b_q)\in D(K\times L),\qquad 1\leq i\leq q.$$

Now define the homotopy $\Phi$ in $K\times L$ by induction as a natural homomorphism. Set $\Phi(a_0\times b_0)=0$. If $\Phi:(K\times L)_{q-1}\to(K\times L)_q$ is defined, for $q>0$, so is the derived operator $\Phi':(K\times L)_q\to(K\times L)_{q+1}$. We define $\Phi$ in dimension $q>0$ by

$$(2.13)\qquad \Phi c_q=-\Phi'c_q+h'D_0c_q,\qquad c_q\in(K\times L)_q.$$

Since $h'$, like any derived operator, is frontal, we conclude, by induction, that $\Phi$ is frontal. To show that $\Phi$ maps norms into norms, calculate $\Phi D_id_{q-1}$, for $0\leq i\leq q-1$, $d_{q-1}\in(K\times L)_{q-1}$. If $0<i$, $\Phi'D_i=\delta^iD_{i-1}$ is a norm, by induction, while if $i=0$, $\Phi'D_0=D_0\Phi$ is a norm, since $\Phi$ is frontal. As for the second term in the definition of $\Phi$, we have $h'D_0D_id_{q-1}=h'D_{i+1}D_0d_{q-1}\in D(K\times L)$ by (2.12).

We next prove that $(\partial\Phi+\Phi\partial)c_q=hc_q-c_q$, modulo norms, for any $c_q\in(K\times L)_q$. For $q=0$, this is immediate, while, for $q=1$, it is proved by direct computation, using (2.11) and

$$\Phi(a_1\times b_1)=D_1D_1F_1a_1\times D_0b_1+D_0a_1\times D_1b_1.$$

If the result holds for dimension $q-1\geq 1$, then we have also

$$(\partial'\Phi'+\Phi'\partial')c_q=h'c_q-c_q,\qquad q\geq2.$$

Using (I.3.11) and the definition (2.13), we compute, for argument $c_q$,

$$\partial\Phi=-\partial'\Phi'+\partial h'D_0=-\partial'\Phi'+h'\partial D_0=-\partial'\Phi'+h'-h'D_0\partial'.$$

On the other hand,

$$\Phi\partial'=-\Phi'\partial'+h'D_0\partial',$$

so that

$$(\partial\Phi+\Phi\partial')c_q=-c_q,
\qquad q\geq2.$$

But, by the definition (2.13) and Lemma I.3.3,

$$F_0\Phi=-F_0\Phi'+F_0h'D_0=-F_0\Phi'+h=-\Phi F_0+h.$$

Since $\partial=F_0-\partial'$, these results combine to yield $(\partial\Phi+\Phi\partial)c_q=hc_q-c_q$, as desired.

It remains to prove the annihilation properties (2.4). The first property, $\Phi\nabla=0$, is proved by induction. It is trivial for dimension zero, as $\Phi=0$ there. In higher dimensions, by (2.13),

$$(2.14)\qquad \Phi\nabla(a_p\otimes b_q)=-\Phi'(a_p\nabla b_q)+h'D_0(a_p\nabla b_q).$$

For the first term we expand by the inductive definition (I.5.7) of $\nabla$ to get

$$-\Phi'(a_p\nabla b_q)=-\Phi'(a_p\nabla'D_0b_q)+\varphi(p+1)\Phi'(D_0a_p\nabla'b_q),$$

or only one of these two terms, in the event that $p$ or $q$ is zero, as in (I.5.7a).

Both these terms are norms by the inductive assumption. For the second term of (2.14), observe that $f\nabla=i$ implies $\nabla f\nabla=\nabla$ and hence $h\nabla=\nabla$ and $h'\nabla'=\nabla'$. Thus, since $\nabla$ is a frontal operator, $h'D_0\nabla=h'\nabla'D_0=\nabla'D_0=D\nabla$ is a norm, q.e.d.

To establish the second annihilation property $f\Phi=0$, we first claim that $\Phi$ can be written as a linear combination of operators $P$ of the form

$$(2.15)\qquad P(a_q\times b_q)=D_j\beta^*a_q\times D_k\gamma^*b_q,
\qquad j\leq k,$$

where $\beta,\gamma:[q]\to[q]$ are monotonic maps. Indeed, the definition of $f$ (with the zero face $F_0$ always in the second factor) shows at once that $h$ is a linear combination of operators $\beta^*a_q\times\gamma^*b_q$, with $\beta$ frontal. As in Lemma I.3.3, this implies that $\beta'^*D_0=D_0\beta^*$. Hence in the second term $h'D_0(a_q\times b_q)=h'(D_0a_q\times D_0b_q)$ of (2.13) we obtain operators of the form (2.15) with $j=0$, and hence necessarily $j\leq k$. The assertion as to the form (2.15) of $\Phi$ then follows by induction.

It now suffices to show for each such $P$ that

$$f_iP(a_q\times b_q)=F^{\,q-i}D_j\beta^*a_q\otimes F_0^{\,i}D_k\gamma^*b_q$$

is a norm. In case $j<i$, the first factor is a norm by (2.7). In case $j\geq i$, we have also $k\geq i$ by the stated form of $P$, and the second factor is a norm by (2.6).

An alternative homotopy $\Psi$ may be obtained by setting

$$\Psi(a\times b)=-\Psi'(a\times b)+h'D_0(a\times b)-D_1F^{\,q}a\times D_0b,$$

for $a\in K_q$, $b\in L_q$. This definition has the effect of removing from $h'D_0$ the term $D_1F^{\,q}\times D_0$ which is otherwise present. It can be shown that $\partial\Psi+\Psi\partial=h-i$, not modulo norms.

A straightforward iteration of the theorem yields:

**Corollary 2.2.** *If $K^{(i)}$, for $i=1,\ldots,t$, are $FD$-complexes, then there exist chain equivalences*

$$K^{(1)}\times\cdots\times K^{(t)}\ \underset{\nabla}{\overset{f}{\rightleftarrows}}\ K^{(1)}\otimes\cdots\otimes K^{(t)}$$

*defined by the formulas*

$$\nabla(a^{(1)}\otimes\cdots\otimes a^{(t)})=a^{(1)}\nabla\cdots\nabla a^{(t)},\qquad a^{(i)}\in K^{(i)},$$

$$f(a^{(1)}\times\cdots\times a^{(t)})=
\sum F^{\,q-j_1}a^{(1)}\otimes F^{\,j_1-j_2}F_0^{\,q-j_1}a^{(2)}\otimes\cdots\otimes F_0^{\,j_{t-1}}a^{(t)},$$

*where in the second formula each $a^{(i)}\in K_q^{(i)}$, and the summation is taken over all $j_i$ with*

$$0\leq j_{t-1}\leq\cdots\leq j_1\leq q.$$

[^1]: Samuel Eilenberg and Saunders Mac Lane, “On the groups $H(\Pi,n)$, I,” *Annals of Mathematics* 58 (1953), 55–106. References to sections and theorems of this paper are made by placing the prefix I on the section or theorem number. The bibliography below is a continuation of that of I; numbers [1] to [9] inclusive refer to the bibliography of I.

[^2]: A portion of this investigation was done under contracts AF-18(600)-562 and Nonr-218(00).
