# DANGER3
Data Challenge for the DANGER workshop at BIRS, April 6-10, 2026

For the purpose of this repository, a **Pomerance triple** is a triple of integers $(p,A,x_0)$ in which $p$ is an odd integer and $A$ and $x_0$ are nonegative integers bounded by $p$ with $A\ne \pm 2 \bmod p$, such that there exist integers $B$ and $y_0$ for which the $(x_0,y_0)$ is a rational point on the [Montgomery curve](https://en.wikipedia.org/wiki/Montgomery_curve) $By^2 = x^3 + Ax^2 +X$ of order $2^k$, where $k$ is the least integer for which $2^k > q + 1 + 2\sqrt{q}$ with $q=\lfloor\sqrt{p}\rfloor$.

More precisely, this means that if one applies the doubling law for Montgomery curves $k-1$ times to the point projective point with coordinates $(x_0:1)$ working modulo the integer $p$, the resulting point will have $z$-coordinate coprime to $p$, but after the $k$th doubling the point will have $z$ coordinate congruent to zero modulo $p$.

This is a minor refinement of the definition used in Pomerance's [paper](https://math.dartmouth.edu/~carlp/PDF/paper62.pdf).  One can adapt Pomerance's result to show that Pomerance triples exist for all primes $p>3$.

This repository contains the following resources:

- vpp.py is a Python program to efficiently verify a candidate Pomerance triple
- lean_vpp.py is a Python program that generates lean code to formally certify a given Pomerance triple
- pp10.txt contains all Pomerance triples $(p,A,x_0)$ with $p\le 2^{10}$.
- pp12.txt.gz contains all Pomerance triples $(p,A,x_0)$ with $p\le 2^{12}$.
- pp16A.txt.gz contains all distinct prefixes $(p,A)$ Pomerance triples with $p\le 2^{16}$.
- pp20.txt containes one Pomerance triple $(p,A,x_0)$ for each prime $3<p<2^{20}$.
- pp24.txt.gz contains one Pomerance triple $(p,A,x_0)$ for each prime $3<p<2^{20}$.
- slides.pdf contains the slides from the presentation used to explain the Data Challenge.

Larger data sets are available at the following locations:
- [pp14.txt.gz](https://math.mit.edu/~drew/pp14.txt.gz): the 43,307,624 Pomerance triples with $p<2^{14}$ (646MB).
- [pp16.txt.gz](https://math.mit.edu/~drew/pp16.txt.gz): the 598,705,640 Pomerance triples with $p<2^{16}$ (9887MB).
- [pp28.txt.gz](https://math.mit.edu/~drew/pp28.txt.gz): one Pomerance triple for each of the 14,630,841 primes $3 < p < 2^{28}$ (386MB).
