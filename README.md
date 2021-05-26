# Program logics: the companion Coq development

This repository contains Coq sources for the course ["Program logics"](https://www.college-de-france.fr/site/xavier-leroy/course-2020-2021.htm) given by Xavier Leroy at Collège de France in 2021.

This is work in progress.

An HTML pretty-printing of the commented sources is also available:

1. Variables and loops: Hoare logics
   * Library [Sequences](https://xavierleroy.org/cdf-program-logics/CDF.Sequences.html): definitions and properties of reduction sequences.
   * Module [Hoare](https://xavierleroy.org/cdf-program-logics/CDF.Hoare.html): Hoare logics for the imperative language IMP.

2. Pointers and data structures: separation logic
   * Library [Separation](https://xavierleroy.org/cdf-program-logics/CDF.Separation.html): definitions and properties of heaps and separation logic assertions.
   * Module [Seplog](https://xavierleroy.org/cdf-program-logics/CDF.Seplog.html): separation logic for the functional/imperative language PTR.

3. Shared-memory concurrency: concurrent separation logic
   * Module [CSL](https://xavierleroy.org/cdf-program-logics/CDF.CSL.html): concurrent separation logic for the PTR language + parallel and atomic constructs.

4. Hoare monads and Dijkstra monads
   * Library [Delay](https://xavierleroy.org/cdf-program-logics/CDF.Delay.html) (coinductive definition of possibly nonterminating computations).
   * Module [Monads](https://xavierleroy.org/cdf-program-logics/CDF.Monads.html)
