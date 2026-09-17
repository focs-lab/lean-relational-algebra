# Attribution and modification notice

This project translates and extends **Damien Pous's relation-algebra library for
Rocq/Coq** in Lean 4 with Mathlib. The upstream source used for the porting inventory is
revision [`2d2af3631929399bbac56f57b3e15302d8697e1c`](https://github.com/damien-pous/relation-algebra/tree/2d2af3631929399bbac56f57b3e15302d8697e1c).

Upstream's [README license notice](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/README.md#license)
and [package metadata](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/rocq-relation-algebra.opam)
specify **LGPL-3.0-or-later**. The complete `COPYING` and `COPYING.LESSER` files here are
verbatim copies from that revision. The same license is used for this translation and
its extensions; we do not treat a change of proof-assistant language as removing
upstream's licensing requirements.

## Upstream attribution

The upstream [AUTHORS](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/AUTHORS)
and [CONTRIBUTORS](https://github.com/damien-pous/relation-algebra/blob/2d2af3631929399bbac56f57b3e15302d8697e1c/CONTRIBUTORS)
files name:

- Damien Pous.
- Christian Doczkal (2018–2021).
- Insa Stucke (2015–2016).
- Rocq development team (2013–).

These credits are retained for the upstream work; they do not imply authorship or
endorsement of this Lean implementation. Christian Doczkal developed the upstream
finite-relation model. [PORTING.md](PORTING.md) maps the developments module by module;
the source documentation identifies the upstream compiler-optimization and Paterson
examples explicitly. Mathematical sources are listed in [the references](docs/REFERENCES.md).

## Changes in this distribution

**2026-09-14 through 2026-09-17:** the Lean source files in `RelationAlgebra/` and the
root import module were written as translations, adaptations, and extensions of the
Rocq/Coq development. Changes include Mathlib-based interfaces, Lean proof reconstruction
and tactics, alternative completeness constructions, typed expression quotients, and
model APIs. These are modified implementations, not the original upstream source files.
The repository history and [development record](docs/DEVELOPMENT_HISTORY.md) identify
the changes and their dates. Release documentation, licensing notices, and CI were
prepared on 2026-09-17.

Lean translation and extensions: Copyright (c) 2026 Umang Mathur and contributors.

OpenAI Codex was used to translate and extend Damien Pous's relation-algebra library from Rocq/Coq to Lean 4.

Lean, Mathlib, and other dependencies retain their own notices and licenses, listed in
[THIRD_PARTY.md](THIRD_PARTY.md). This notice records provenance and changes; it does not
add restrictions to the licenses.
