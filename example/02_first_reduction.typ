#import "common.typ": *

= First reductions of the problem <first-reduction>

== Overview

The proof of Fermat's Last Theorem is by contradiction. We assume that we have a
counterexample $a^n + b^n = c^n$, and manipulate it until it satisfies the
axioms of a "Frey package". From the Frey package we build a Frey curve --- an
elliptic curve defined over the rationals. We then look at a certain
representation of a Galois group coming from this elliptic curve, and finally
using two very deep and independent theorems (one due to Mazur, the other due to
Wiles) we show that this representation is neither reducible or irreducible, a
contradiction.

== Reduction to $n >= 5$ and prime

#lemma(
  lean: <FermatLastTheorem.of_odd_primes>,
)[
  If there is a counterexample to Fermat's Last Theorem, then there is a
  counterexample $a^p + b^p = c^p$ with an odd prime $p$.
][
  Note: this proof is #link(
    "https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/FLT/Four.html#FermatLastTheorem.of_odd_primes",
  )[in mathlib already];; we run through it for completeness' sake.


  Say $a^n + b^n = c^n$ is a counterexample to Fermat's Last Theorem. Every
  positive integer is either a power of 2 or has an odd prime factor. If
  $n = k p$ has an odd prime factor $p$ then $(a^k)^p + (b^k)^p = (c^k)^p$ is
  the counterexample we seek. It remains to deal with the case where $n$ is a
  power of 2, so let's assume this. We have $3 <= n$ by assumption, so $n = 4 k$
  must be a multiple of 4, and thus $(a^k)^4 + (b^k)^4 = (c^k)^4$, giving us a
  counterexample to Fermat's Last Theorem for $n = 4$. However an old result of
  Fermat himself (proved as #link(
    "https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/FLT/Four.html#fermatLastTheoremFour",
  )[`fermatLastTheoremFour`] in mathlib) says that $x^4 + y^4 = z^4$ has no
  solutions in positive integers.
]

Euler proved Fermat's Last Theorem for $p = 3$;

#lemma(
  lean: <fermatLastTheoremThree>,
)[
  There are no solutions in positive integers to $a^3 + b^3 = c^3$.
][
  The proof in mathlib was formalized by a team from the "Lean For the Curious
  Mathematician" conference held in Luminy in March 2024 (its dependency graph
  can be visualised #link(
    "https://pitmonticone.github.io/FLT3/blueprint/dep_graph_document.html",
  )[here]).
]

#corollary(
  lean: <FLT.of_p_ge_5>,
  uses: (<fermatLastTheoremThree>, <FermatLastTheorem.of_odd_primes>),
)[
  If there is a counterexample to Fermat's Last Theorem, then there is a
  counterexample $a^p + b^p = c^p$ with $p$ prime and $p >= 5$.
][
  Follows from the previous two lemmas.
]

== Frey packages

For convenience we make the following definition.

#definition(
  lean: <FLT.FreyPackage>,
)[
  A _Frey package_ $(a, b, c, p)$ is three pairwise-coprime nonzero integers
  $a$, $b$, $c$, with $a eq.triple 3 thick (mod 4)$ and
  $b eq.triple 0 thick (mod 2)$, and a prime $p >= 5$, such that
  $a^p + b^p = c^p$.
]

Our next reduction is as follows:

#lemma(
  lean: <FLT.FreyPackage.of_not_FermatLastTheorem_p_ge_5>,
  uses: (<FLT.FreyPackage>,),
)[
  If Fermat's Last Theorem is false for $p >= 5$ and prime, then there exists a
  Frey package.
][
  Suppose we have a counterexample $a^p + b^p = c^p$ for the given $p$; we now
  build a Frey package from this data.

  If the greatest common divisor of $a, b, c$ is $d$ then $a^p + b^p = c^p$
  implies $(a/d)^p + (b/d)^p = (c/d)^p$. Dividing through, we can thus assume
  that no prime divides all of $a, b, c$. Under this assumption we must have
  that $a, b, c$ are pairwise coprime, as if some prime divides two of the
  integers $a, b, c$ then by $a^p + b^p = c^p$ and unique factorization it must
  divide all three of them. In particular we may assume that not all of
  $a, b, c$
  are even, and now reducing modulo 2 shows that precisely one of them must be
  even.

  Next we show that we can find a counterexample with $b$ even. If $a$ is the
  even one then we can just switch $a$ and $b$. If $c$ is the even one then we
  can replace $c$ by $-b$ and $b$ by $-c$ (using that $p$ is odd).

  The last thing to ensure is that $a$ is 3 mod 4. Because $b$ is even, we know
  that $a$ is odd, so it is either 1 or 3 mod 4. If $a$ is 3 mod 4 then we are
  home; if however $a$ is 1 mod 4 we replace $a, b, c$ by their negatives and
  this is the Frey package we seek.
]

== Galois representations and elliptic curves

To continue, we need some of the theory of elliptic curves over $QQ$. So let
$f(X)$ denote any monic cubic polynomial with rational coefficients and whose
three complex roots are distinct, and let us consider the equation
$E : Y^2 = f(X)$, which defines a curve in the $(X, Y)$ plane. This curve (or
strictly speaking its projectivisation) is a so-called elliptic curve (or an
elliptic curve over $QQ$ if we want to keep track of the field where the
coefficients of $f(X)$ lie). More generally if $k$ is any field then there is a
concept of an elliptic curve over $k$, again defined by a (slightly more
general) plane cubic curve $F(X, Y) = 0$.

If $E$ is an elliptic curve over a field $k$, and if $K$ is any field which is a
$k$-algebra, then we write $E(K)$ for the set of solutions to $y^2 = f(x)$with
$x, y in K$, together with an additional "point at infinity". It is an
extraordinary fact, and not at all obvious, that $E(K)$ naturally has the
structure of an additive abelian group, with the point at infinity being the
zero element (the identity). Fortunately this fact is already in mathlib. We
shall use $+$ to denote the group law. This group structure has the property
that three distinct points $P, Q, R in K^2$ which are in $E(K)$ will sum to zero
if and only if they are collinear.

The group structure behaves well under change of field.

#lemma(
  lean: <WeierstrassCurve.Points.map>,
)[
  If $E$ is an elliptic curve over a field $k$, and if $K$ and $L$ are two
  fields which are $k$-algebras, and if $f : K -> L$ is a $k$-algebra
  homomorphism, the map from $E(K)$ to $E(L)$ induced by $f$ is an additive
  group homomorphism.
][
  The equations defining the group law are ratios of polynomials with
  coefficients in $k$, and such things behave well under $k$-algebra
  homomorphisms.
]

This construction is functorial (it sends the identity to the identity, and
compositions to compositions).

#lemma(
  lean: <WeierstrassCurve.Points.map_id>,
  uses: (<WeierstrassCurve.Points.map>,),
)[
  The group homomorphism $E(K) -> E(K)$ induced by the identity map $K -> K$ is
  the identity group homomorphism.
][
  An easy calculation.
]

#lemma(
  lean: <WeierstrassCurve.Points.map_comp>,
  uses: (<WeierstrassCurve.Points.map>,),
)[
  If $K -> L -> M$ are $k$-algebra homomorphisms then the group homomorphism
  $E(K) -> E(M)$
  induced by the map $K -> M$ is the composite of the map $E(K) -> E(L)$ induced
  by $K -> L$ and the map $E(L) -> E(M)$ induced by the map $L -> M$.
][
  Another easy calculation.
]

Thus if $f : K -> L$ is an isomorphism of fields, the induced map $E(K) -> E(L)$
is an isomorphism of groups, with the inverse isomorphism being the map
$E(L) -> E(K)$ induced by $f^-1$. This construction thus gives us an action of
the multiplicative group $"Aut"_k(K)$ of $k$-automorphisms of the field $K$ on
the additive abelian group $E(K)$.

#definition(
  lean: <WeierstrassCurve.galoisRepresentation>,
  uses: (<WeierstrassCurve.Points.map_id>, <WeierstrassCurve.Points.map_comp>),
)[
  If $E$ is an elliptic curve over a field $k$ and $K$ is a field and a
  $k$-algebra, then the group of $k$-automorphisms of $K$ acts on the additive
  abelian group $E(K)$.
]

In particular, if $overline(QQ)$ denotes an algebraic closure of the rationals
(for example, the algebraic numbers in $CC$) and if
$"Gal"(overline(QQ) slash QQ)$ denotes the group of field isomorphisms
$overline(QQ) -> overline(QQ)$, then for any elliptic curve $E$ over $QQ$ we
have an action of $"Gal"(overline(QQ) slash QQ)$ on the additive abelian group
$E(overline(QQ))$.

We need a variant of this construction where we only consider the $n$-torsion of
the curve, for $n$ a positive integer. Recall that if $A$ is any additive
abelian group, and if $n$ is a positive integer, then we can consider the
subgroup $A[n]$ of elements $a$ such that $n a = 0$. If a group $G$ acts on $A$
via additive group isomorphisms, then there will be an induced action of $G$ on
$A[n]$.

#definition(
  lean: <WeierstrassCurve.torsionGaloisRepresentation>,
  uses: (<WeierstrassCurve.galoisRepresentation>,),
)[
  If $E$ is an elliptic curve over a field $k$ and $K$ is a field and a
  $k$-algebra, and if $n$ is a natural number, then the group of
  $k$-automorphisms of $K$ acts on the additive abelian group $E(K)[n]$ of
  $n$-torsion points on the curve.
]

If furthermore $n = p$ is prime, then $A[p]$ is naturally a vector space over
the field $ZZ slash p ZZ$, and thus it inherits the structure of a mod $p$
representation of $G$. Applying this to the above situation, we deduce that if
$E$ is an elliptic curve over $QQ$ then $"Gal"(overline(QQ) slash QQ)$ acts on
$E(overline(QQ))[p]$ and this is the _mod $p$ Galois representation_ attached to
the curve $E$.

In the next section we apply this theory to an elliptic curve coming from a
counterexample to Fermat's Last theorem.
