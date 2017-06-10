<!--
  vim: filetype=markdown
-->

[![Build Status][build-status-badge]][build-status-link]
[![Ready Stories][tickets-badge]][tickets-link]

[build-status-badge]: https://travis-ci.org/waylang/metatheory.svg?branch=master
[build-status-link]: https://travis-ci.org/waylang/metatheory
[tickets-badge]: https://badge.waffle.io/waylang/metatheory.png?label=ready&title=Ready
[tickets-link]: http://waffle.io/waylang/metatheory

# Metatheory

Formal Specification

## About

Metatheory is a [Coq][coq] implementation of Way's underlying mathematical theory
("metatheory").  It contains machine-verified proofs of critical properties of the
language (or rather of its implementation within Coq, see "Adequacy").  Successful runs
of the build script demonstrate the verification.

[coq]: https://coq.inria.fr/

### Adequacy

**TODO(phs)**: adequacy

## Getting Started

```
$ cd metatheory
$ vagrant up
$ vagrant ssh
ubuntu@metatheory:~$ cd metatheory
ubuntu@metatheory:~/metatheory$ make
```

## References

* Chlipala. [Certified Programming with Dependent Types][cert-prog]. MIT Press, 2014.
  `[cert-prog]`

[cert-prog]: http://adam.chlipala.net/cpdt/

* Coquand, Huet. [The Calculus of Constructions][coc]. Information and Computation, 1988.
  `[coc]`

[coc]: http://www.sciencedirect.com/science/article/pii/0890540188900053

* Barras, Werner. [Coq in coq][coq-in-coq]. 1997. `[coq-in-coq]`

[coq-in-coq]: http://pauillac.inria.fr/~barras/coq_work-eng.html

* Aydemir, Chargue ́raud, Pierce et al. [Engineering Formal Metatheory][eng-formal-meta].
  POPL, 2008. `[eng-formal-meta]`

[eng-formal-meta]: http://www.seas.upenn.edu/~sweirich/papers/popl08-binders.pdf

* Paulin-Mohring. [Introduction to the Calculus of Inductive Constructions][intro-cic].
  2014. `[intro-cic]`

[intro-cic]: https://hal.inria.fr/hal-01094195/file/CIC.pdf

* Altenkirch, McBride, Swierstra. [Observational Equality, Now!][obs-eq-now], PLPV, 2007.
  `[obs-eq-now]`

[obs-eq-now]: http://www.cs.nott.ac.uk/~psztxa/publ/obseqnow.pdf

* Altenkirch, McBride. [Towards Observational Type Theory][towards-ott]. `[towards-ott]`

[towards-ott]: http://strictlypositive.org/ott.pdf

* Pierce. [Types and Programming Languages][types-and-lang]. MIT Press, 2002.
  `[types-and-lang]`

[types-and-lang]: http://www.cis.upenn.edu/~bcpierce/tapl/index.html

* Herbelin. [Type inference with algebraic universes in the Calculus of Inductive
  Constructions][infer-algebraic-uni]. `[infer-algebraic-uni]`

[infer-algebraic-uni]: http://pauillac.inria.fr/~herbelin/articles/univalgcci.pdf

## License

Copyright (C) 2016-2017 Philip H. Smith

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
