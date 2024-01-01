<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Regular Language Representations in Coq

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/reglang/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/reglang/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://coq-community.org/reglang

[doi-shield]: https://zenodo.org/badge/DOI/10.1007/s10817-018-9460-x.svg
[doi-link]: https://doi.org/10.1007/s10817-018-9460-x

This library provides definitions and verified translations between
different representations of regular languages: various forms of
automata (deterministic, nondeterministic, one-way, two-way),
regular expressions, and the logic WS1S. It also contains various
decidability results and closure properties of regular languages.

## Meta

- Author(s):
  - Christian Doczkal (initial)
  - Jan-Oliver Kaiser (initial)
  - Gert Smolka (initial)
- Coq-community maintainer(s):
  - Christian Doczkal ([**@chdoc**](https://github.com/chdoc))
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [CeCILL-B](LICENSE)
- Compatible Coq versions: 8.16 or later (use releases for other Coq versions)
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 2.0 or later (`ssreflect` suffices)
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) 1.4.0 or later
- Coq namespace: `RegLang`
- Related publication(s):
  - [Regular Language Representations in the Constructive Type Theory of Coq](https://hal.archives-ouvertes.fr/hal-01832031/document) doi:[10.1007/s10817-018-9460-x](https://doi.org/10.1007/s10817-018-9460-x)

## Building and installation instructions

The easiest way to install the latest released version of Regular Language Representations in Coq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-reglang
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/reglang.git
cd reglang
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## HTML Documentation

To generate HTML documentation, run `make coqdoc` and point your browser at `docs/coqdoc/toc.html`.

See also the pregenerated HTML documentation for the [latest release](https://coq-community.org/reglang/docs/latest/coqdoc/toc.html).

## File Contents

* `misc.v`, `setoid_leq.v`: basic infrastructure independent of regular languages
* `languages.v`: languages and decidable languages
* `dfa.v`:
  * results on deterministic one-way automata
  * definition of regularity
  * criteria for nonregularity
* `nfa.v`: Results on nondeterministic one-way automata
* `regexp.v`: Regular expressions and Kleene Theorem
* `minimization.v`: minimization and uniqueness of minimal DFAs
* `myhill_nerode.v`: classifiers and the constructive Myhill-Nerode theorem
* `two_way.v`: deterministic and nondeterministic two-way automata
* `vardi.v`: translation from 2NFAs to NFAs for the complement language
* `shepherdson.v`: translation from 2NFAs and 2DFAs to DFAs (via classifiers)
* `wmso.v`:
  * decidability of WS1S
  * WS1S as representation of regular languages
