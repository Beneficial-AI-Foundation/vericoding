-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dsplit {n k : Nat} (arr : Vector Float (k * n)) (sections : Nat) 
  (h : sections = k ∧ k > 0) : Id (List (Vector Float n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dsplit_spec {n k : Nat} (arr : Vector Float (k * n))
  (h : k > 0) :
  ⦃⌜k > 0⌝⦄
  dsplit arr k ⟨rfl, h⟩
  ⦃⇓result => ⌜result.length = k ∧
              ∀ i : Fin k, ∃ sub ∈ result,
                ∀ j : Fin n, sub.get j = arr.get ⟨i.val * n + j.val, by
                  have h1 : i.val < k := i.isLt
                  have h2 : j.val < n := j.isLt
                  calc i.val * n + j.val
                    < i.val * n + n := Nat.add_lt_add_left h2 _
                    _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
                    _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
                ⟩⌝⦄ := by
  sorry
-- </vc-theorems>