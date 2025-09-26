import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper function to compute differences between consecutive elements
def diff_at {n : Nat} (ary : Vector Float (n + 1)) (i : Fin n) : Float :=
  ary.get (i.succ) - ary.get (i.castSucc)

-- Helper function to build the result vector
def build_diff_vector {n : Nat} (ary : Vector Float (n + 1)) : Vector Float n :=
  Vector.ofFn (diff_at ary)
-- </vc-helpers>

-- <vc-definitions>
def numpy_ediff1d {n : Nat} (ary : Vector Float (n + 1)) : Id (Vector Float n) :=
  pure (build_diff_vector ary)
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_ediff1d_spec {n : Nat} (ary : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_ediff1d ary
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = ary.get (i.succ) - ary.get (i.castSucc)⌝⦄ := by
  -- LLM HELPER
-- First prove that our implementation computes the right values
have numpy_ediff1d_unfold : numpy_ediff1d ary = pure (Vector.ofFn (diff_at ary)) := by rfl
-- Main proof
simp [numpy_ediff1d_unfold]
intro i
simp [Vector.get_ofFn, diff_at]
-- </vc-theorems>
