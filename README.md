# Regular Language Representations in the Constructive Type Theory of Coq #

This repository contains the coq development accompanying the paper: 

[Christian Doczkal](https://perso.ens-lyon.fr/christian.doczkal/) and [Gert Smolka](https://www.ps.uni-saarland.de/~smolka/), _Regular Language Representations in the Constructive Type Theory of Coq_, J. Autom. Reason. - Special Issue on Milestones in Interactive Theorem Proving, Springer, 2018. 

## Prerequisites 

One of the following:

* coq-8.8 + mathcomp-1.7.0 (the ssreflect component)
* coq-8.7 + mathcomp-1.6.4 (the ssreflect component)
* coq-8.6 + mathcomp-1.6.1 (the ssreflect component)

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
