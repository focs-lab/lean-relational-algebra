# References

The main mathematical and mechanization references are:

- **Damien Pous (2013).** [Kleene Algebra with Tests and Coq Tools for While Programs](https://arxiv.org/abs/1302.1737). KAT formalization and automation.
- **Dexter Kozen and Maria-Cristina Patron (2000).** [Certification of Compiler Optimizations Using Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/opti.pdf). The compiler-optimization examples.
- **Chris Hardin and Dexter Kozen (2002).** [On the Elimination of Hypotheses in Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/elim.pdf). Hypothesis elimination for `hkat`; this library proves soundness but not elimination completeness.
- **Allegra Angus and Dexter Kozen (2001).** [Kleene Algebra with Tests and Program Schematology](https://www.cs.cornell.edu/~kozen/Papers/allegra.pdf). Paterson’s flowchart equivalence (§5); our proof follows [Pous’s mechanization](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/examples/paterson.v).
- **Dexter Kozen (1994).** [A Completeness Theorem for Kleene Algebras and the Algebra of Regular Events](https://www.cs.cornell.edu/~kozen/papers/ka.pdf). KA axioms, matrices, and completeness.
- **Dexter Kozen (1997).** [Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf). The KAT framework.
- **Dexter Kozen (2000).** [On Hoare Logic and Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/Hoare.pdf). The algebraic encoding of partial correctness.
- **Dexter Kozen and Frederick Smith (CSL 1996).** [Kleene Algebra with Tests: Completeness and Decidability](https://www.cs.cornell.edu/~kozen/Papers/gs.pdf). Guarded strings and KAT completeness; both untyped and typed forms are proved here.
- **Valentin Antimirov (1996).** [Partial Derivatives of Regular Expressions and Finite Automaton Constructions](https://doi.org/10.1016/0304-3975(95)00182-4). The partial-derivative construction.
- **Alexander Krauss and Tobias Nipkow (2012).** [Proof Pearl: Regular Expression Equivalence and Relation Algebra](https://www21.in.tum.de/~nipkow/pubs/jar12.pdf). Verified equivalence checking and its application to relations.
- **Alfred Tarski (1941).** [On the Calculus of Relations](https://doi.org/10.2307/2268577). Foundations of relation algebra.
