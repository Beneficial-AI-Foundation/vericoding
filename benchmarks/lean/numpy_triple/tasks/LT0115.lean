-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_as_strided {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) : Id (Vector Float m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_as_strided_spec {n m : Nat} (x : Vector Float n) (stride : Nat) 
    (h_valid : m * stride ≤ n) (h_stride_pos : stride > 0) :
    ⦃⌜m * stride ≤ n ∧ stride > 0⌝⦄
    numpy_as_strided x stride h_valid h_stride_pos
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = x.get ⟨i.val * stride, 
                   by have h1 : i.val < m := i.isLt
                      have h2 : i.val * stride < m * stride := by
                        apply Nat.mul_lt_mul_of_pos_right h1 h_stride_pos
                      exact Nat.lt_of_lt_of_le h2 h_valid⟩⌝⦄ := by
  sorry
-- </vc-theorems>