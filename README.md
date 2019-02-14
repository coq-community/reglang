# Regular Language Representations in the Constructive Type Theory of Coq #

This repository contains the Coq development accompanying the paper:

[Christian Doczkal](https://perso.ens-lyon.fr/christian.doczkal/) and [Gert Smolka](https://www.ps.uni-saarland.de/~smolka/), _Regular Language Representations in the Constructive Type Theory of Coq_, J. Autom. Reason. - Special Issue on Milestones in Interactive Theorem Proving, Springer, 2018. 

## Prerequisites 

One of the following:

* [coq-8.9](https://github.com/coq/coq/releases/tag/V8.9.0) + [mathcomp-1.7.0](https://github.com/math-comp/math-comp/releases/tag/mathcomp-1.7.0) (the ssreflect component)
* [coq-8.8](https://github.com/coq/coq/releases/tag/V8.8.2) + [mathcomp-1.7.0](https://github.com/math-comp/math-comp/releases/tag/mathcomp-1.7.0) (the ssreflect component)
* [coq-8.7](https://coq.inria.fr/coq-87) + [mathcomp-1.6.4](https://github.com/math-comp/math-comp/releases/tag/mathcomp-1.6.4) (the ssreflect component)
* [coq-8.6](https://coq.inria.fr/coq-86) + [mathcomp-1.6.1](https://github.com/math-comp/math-comp/releases/tag/mathcomp-1.6.1) (the ssreflect component)

## Building and Installation

The easiest way to install the library is via [OPAM](https://opam.ocaml.org/):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-reglang
```

To instead build and install the library manually, run `make` followed by `make install`.

## HTML Documentation

To generate the HTML documentation, run `make website` and point your browser at `website/toc.html`

Pregenerated HTML documentation (and a pre-print of the paper) can be found at: https://www.ps.uni-saarland.de/extras/RLR-Coq

## File Contents

* misc.v, setoid_leq.v:	basic infrastructure independent of regular languages
* languages.v: languages and decidable languages
* dfa.v: 
  * results on deterministic one-way automata
  * definition of regularity
  * criteria for nonregularity
* nfa.v: Results on nondeterministic one-way automata
* regexp.v: Regular expressions and Kleene Theorem
* minimization.v: minimization and uniqueness of minimal DFAs
* myhill_nerode.v: classifiers and the constructive Myhill-Nerode theorem
* two_way.v: deterministic and nondeterministic two-way automata
* vardi.v: translation from 2NFAs to NFAs for the complement language
* shepherdson.v: translation from 2NFAs and 2DFAs to DFAs (via classifiers)
* wmso.v: 
  * decidability of WS1S
  * WS1S as representation of regular languages
