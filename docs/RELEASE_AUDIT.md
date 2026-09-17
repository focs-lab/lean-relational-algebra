# Source-release review — 2026-09-17

This review covers the release-preparation worktree based on commit `00c9485`, the pinned
Lean/Mathlib 4.30.0 environment, and the reachable Git history. It concerns a source release;
it does not certify a separately assembled binary or toolchain distribution.

## Licensing and provenance

- Upstream revision `2d2af3631929399bbac56f57b3e15302d8697e1c` specifies
  **LGPL-3.0-or-later** in its README and package metadata. The project now uses the same
  terms. Both required license texts were compared byte-for-byte with upstream.
- [NOTICE.md](../NOTICE.md) preserves the upstream author/contributor credits, identifies
  the translation and modifications with dates, and records Codex's use. The module-level
  correspondence remains in [PORTING.md](../PORTING.md).
- All nine locked dependencies' top-level license files were inspected: eight Apache-2.0,
  one MIT. They are fetched separately, not vendored. [THIRD_PARTY.md](../THIRD_PARTY.md)
  links their exact revisions and license files and explains the scope of that inventory.
- The mathematical references include the sources for compiler optimizations and
  hypothesis elimination. Papers are linked rather than redistributed.

The review fixes the missing license and attribution packaging. It is not a legal opinion
or a guarantee against every third-party claim. Repository inspection cannot establish
employer/university ownership, contributor authority, patent rights, or contractual
restrictions. Maintainers must have authority to release their contributions under the
stated terms; the copyright notice currently names Umang Mathur and contributors.

## Repository hygiene

- A pattern scan of all 201 reachable historical blobs found no common GitHub, AWS,
  OpenAI-style, or Slack token patterns, private-key blocks, credential-bearing URLs,
  or machine-local source paths. This is a bounded scan, not proof that no secret exists.
- No tracked build products, dependency caches, or binary attachments were found.
- The stale lockfile package name was corrected without changing dependency revisions.
- The README is a short entry point; the detailed guide and development history are
  preserved separately. No mathematical declarations were changed in this pass.

## Validation

Run the reproducible checks in [CONTRIBUTING.md](../CONTRIBUTING.md):

- `lake build --wfail`: 1,566 jobs, no warnings.
- The whole-library axiom audit checked **6,471 declarations**, including generated
  declarations; 2,735 use no axioms, and the rest use only `propext`, `Classical.choice`,
  and `Quot.sound`. Temporary negative probes confirmed rejection of a new axiom and
  an admitted proof.
- All seven Lean examples in the README and guide compile. Local documentation links
  resolve, and all 110 library modules are reachable from the root import. Temporary
  negative probes confirmed rejection of a broken link and an unimported module.
- A fresh downstream package built a local source snapshot of the library and the README
  examples, plus finite-relation and setoid-relation tactic examples: **1,568 jobs, no
  warnings**. No library build artifacts were copied; only the pinned third-party
  dependency cache was reused. All nine resolved dependency revisions matched the lockfile.
  This tests local package integration, not anonymous installation from GitHub.

The new GitHub Actions workflow uses read-only repository permissions and pinned action
revisions. Its inputs were checked against the pinned Lean action. The hosted workflow
must run after these changes are pushed; no hosted CI result is claimed here.

The repository remains private. Anonymous cloning cannot be tested until publication;
this review does not change visibility, create a release, or publish compiled artifacts.
