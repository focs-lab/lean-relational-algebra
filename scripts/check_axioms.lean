/- SPDX-License-Identifier: LGPL-3.0-or-later
Copyright (c) 2026 Umang Mathur and contributors. See LICENSE and NOTICE.md. -/
import RelationAlgebra
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut noAxioms := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`RelationAlgebra).isPrefixOf env.header.moduleNames[idx]! then
        if info matches .axiomInfo _ then
          throwError "New library axiom: {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        count := count + 1
        if axioms.isEmpty then noAxioms := noAxioms + 1
  if count == 0 then throwError "No library declarations were audited"
  logInfo m!"Audited {count} library declarations ({noAxioms} without axioms); all others use only propext, Classical.choice, Quot.sound."
