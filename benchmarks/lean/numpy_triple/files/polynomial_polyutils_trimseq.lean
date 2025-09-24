-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trimseq {n : Nat} (seq : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trimseq_spec {n : Nat} (seq : Vector Float n) :
    ⦃⌜True⌝⦄
    trimseq seq
    ⦃⇓result => ⌜-- Result has same length as input
                 result.toList.length = n ∧
                 -- If empty or last element is non-zero, return unchanged
                 (n = 0 ∨ (n > 0 ∧ seq.get ⟨n - 1, sorry⟩ ≠ 0) → result = seq) ∧
                 -- If last element is zero, trim properly
                 (n > 0 ∧ seq.get ⟨n - 1, sorry⟩ = 0 → 
                   -- There exists a position k where trimming occurs
                   (∃ k : Fin n, 
                    -- All elements after k in original sequence are zero
                    (∀ j : Fin n, j.val > k.val → seq.get j = 0) ∧
                    -- Result preserves elements up to k, zeros after
                    (∀ i : Fin n, i.val ≤ k.val → result.get i = seq.get i) ∧
                    (∀ i : Fin n, i.val > k.val → result.get i = 0) ∧
                    -- Element at k is non-zero unless k = 0 (all zeros case)
                    (k.val > 0 → seq.get k ≠ 0)))⌝⦄ := by
  sorry
-- </vc-theorems>