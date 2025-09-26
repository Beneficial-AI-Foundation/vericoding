import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers required for this simple specification.
-- This section reserved for future lemmas about Vector/Id if needed.
-- </vc-helpers>

-- <vc-definitions>
def size {n : Nat} (a : Vector Float n) : Id Nat :=
  n
-- </vc-definitions>

-- <vc-theorems>
theorem size_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    size a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  simp [size]
  intros _
  rfl
-- </vc-theorems>
