import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Std
open Std.Do

-- </vc-helpers>

-- <vc-definitions>
def shape {α : Type} {n : Nat} (a : Vector α n) : Id Nat :=
  n
-- </vc-definitions>

-- <vc-theorems>
theorem shape_spec {α : Type} {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    shape a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  intro _; rfl
-- </vc-theorems>
