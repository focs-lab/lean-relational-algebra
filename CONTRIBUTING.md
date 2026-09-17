# Contributing

Use the Lean version in `lean-toolchain` and the dependencies in `lake-manifest.json`.
Start with `lake exe cache get`, then run:

```sh
lake build --wfail
lake env lean scripts/check_axioms.lean
python3 scripts/check_docs.py
```

The default build includes the example and regression modules. Some compiler-optimization
proofs take substantially longer than the small examples. CI runs these same checks.
The axiom check covers all declarations emitted by this library, including generated
declarations, and permits only `propext`, `Classical.choice`, and `Quot.sound`.

For proof or tactic changes, add a focused example under `RelationAlgebra/Examples/`.
For tactics, cover relevant invalid goals with `fail_if_success` as well as successful
proofs. Do not introduce `sorry`, `admit`, new axioms, or `native_decide`.
Keep every library module reachable from `RelationAlgebra.lean`; the documentation
check verifies this so the build and axiom audit cannot silently miss a module.

Update the [user guide](docs/GUIDE.md) when behavior changes, and [PORTING.md](PORTING.md)
when upstream coverage changes. Preserve source attribution and identify translations
or adaptations. Submit contributions under the project's [LGPL-3.0-or-later license](LICENSE),
and only include material you have the right to contribute under those terms.

The initial [source-release review](docs/RELEASE_AUDIT.md) records the checks and their limits.
