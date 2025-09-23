-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hsplit {n k : Nat} (arr : Vector Float n) 
    (h_divides : k > 0 ∧ n % k = 0) : 
    Id (Vector (Vector Float (n / k)) k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hsplit_spec {n k : Nat} (arr : Vector Float n) 
    (h_divides : k > 0 ∧ n % k = 0) :
    ⦃⌜k > 0 ∧ n % k = 0⌝⦄
    hsplit arr h_divides
    ⦃⇓result => ⌜(∀ (part_idx : Fin k) (elem_idx : Fin (n / k)),
                  (result.get part_idx).get elem_idx = 
                  arr.get ⟨part_idx.val * (n / k) + elem_idx.val, by sorry⟩) ∧
                 (∀ i : Fin n, ∃ (p : Fin k) (e : Fin (n / k)), 
                  i.val = p.val * (n / k) + e.val ∧
                  arr.get i = (result.get p).get e)⌝⦄ := by
  sorry
-- </vc-theorems>