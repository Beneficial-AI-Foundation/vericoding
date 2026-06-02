import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper function to apply log10 to each element of a vector
def vector_map_log10 {n : Nat} (x : Vector Float n) : Vector Float n :=
  Vector.ofFn (fun i => Float.log10 (x.get i))
-- </vc-helpers>

-- <vc-definitions>
def numpy_log10 {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (vector_map_log10 x)
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_log10_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > 0⌝⦄
    numpy_log10 x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log10 (x.get i)⌝⦄ := by
  unfold numpy_log10
  unfold vector_map_log10
  intro h
  simp [Vector.get_ofFn]
-- </vc-theorems>
