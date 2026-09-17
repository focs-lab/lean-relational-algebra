# Third-party software

The source release does not vendor dependencies or compiled dependency artifacts.
Lake fetches the packages below separately; their own license files and notices remain
in `.lake/packages/`. Exact revisions are recorded in [lake-manifest.json](lake-manifest.json).
The project license does not relicense these packages. The table lists their top-level
licenses; bundled components can carry additional notices, which remain in the fetched
sources (for example, `importGraph`'s HTML template and vendor files).

| Package | Role | Top-level license at the pinned revision |
| --- | --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4/tree/c5ea00351c28e24afc9f0f84379aa41082b1188f) | Direct dependency | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/LICENSE) |
| [plausible](https://github.com/leanprover-community/plausible/tree/a456461b368b71d2accd95234832cd9c174b5437) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/plausible/blob/a456461b368b71d2accd95234832cd9c174b5437/LICENSE) |
| [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient/tree/c5d5b8fe6e5158def25cd28eb94e4141ad97c843) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/LeanSearchClient/blob/c5d5b8fe6e5158def25cd28eb94e4141ad97c843/LICENSE) |
| [importGraph](https://github.com/leanprover-community/import-graph/tree/515cf9d0c00ece5e661f6de4326a53dedc1e8ea1) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/import-graph/blob/515cf9d0c00ece5e661f6de4326a53dedc1e8ea1/LICENSE) |
| [proofwidgets](https://github.com/leanprover-community/ProofWidgets4/tree/a84b3e2475d5c5ab979567b1ad8aea21b764bcf8) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/ProofWidgets4/blob/a84b3e2475d5c5ab979567b1ad8aea21b764bcf8/LICENSE) |
| [aesop](https://github.com/leanprover-community/aesop/tree/558915ae105bfd8074e22d597613d1961822adc2) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/aesop/blob/558915ae105bfd8074e22d597613d1961822adc2/LICENSE) |
| [Qq](https://github.com/leanprover-community/quote4/tree/a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/quote4/blob/a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c/LICENSE) |
| [batteries](https://github.com/leanprover-community/batteries/tree/32dc18cde3684679f3c003de608743b57498c56f) | Transitive dependency | [Apache-2.0](https://github.com/leanprover-community/batteries/blob/32dc18cde3684679f3c003de608743b57498c56f/LICENSE) |
| [Cli](https://github.com/leanprover/lean4-cli/tree/6b907cf12b2e445ccb7c24bc208ef04a1f39e84c) | Transitive dependency | [MIT](https://github.com/leanprover/lean4-cli/blob/6b907cf12b2e445ccb7c24bc208ef04a1f39e84c/LICENSE) |

The [Lean 4.30.0 toolchain](https://github.com/leanprover/lean4/tree/v4.30.0)
is distributed under [Apache-2.0](https://github.com/leanprover/lean4/blob/v4.30.0/LICENSE);
its bundled third-party components retain their own notices. The toolchain is installed
separately and is not part of this source distribution.

Upstream `relation-algebra` is the basis for the translation, rather than a Lake dependency.
Its LGPL-3.0-or-later terms and attribution are recorded in [LICENSE](LICENSE) and
[NOTICE.md](NOTICE.md), with both complete license texts included.

If distributing a bundle containing dependencies, a toolchain, or compiled artifacts,
preserve the applicable license texts and notices from those distributions and satisfy
the corresponding source and relinking requirements where applicable. This inventory
covers the source release, not a separately assembled binary bundle.
