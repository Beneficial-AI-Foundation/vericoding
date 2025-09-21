-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermecompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermecompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_last_nonzero : c.get ⟨n + 1, by omega⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, by omega⟩ ≠ 0⌝⦄
    hermecompanion c
    ⦃⇓mat => ⌜
      -- Matrix is symmetric (superdiagonal equals subdiagonal)
      (∀ i : Fin n, (mat.get ⟨i.val, by omega⟩).get ⟨i.val + 1, by omega⟩ = 
        (mat.get ⟨i.val + 1, by omega⟩).get ⟨i.val, by omega⟩) ∧
      -- Superdiagonal elements are sqrt(i+1) for i = 0 to n-1
      (∀ i : Fin n, (mat.get ⟨i.val, by omega⟩).get ⟨i.val + 1, by omega⟩ = 
        Float.sqrt (Float.ofNat (i.val + 1))) ∧
      -- Last column contains scaled coefficients except for the last element
      (∀ i : Fin (n + 1), (mat.get i).get ⟨n, by omega⟩ = 
        -(c.get ⟨i.val, by omega⟩ / c.get ⟨n + 1, by omega⟩)) ∧
      -- All other elements are zero (excluding superdiagonal, subdiagonal, and last column)
      (∀ i j : Fin (n + 1), j.val ≠ i.val + 1 ∧ j.val ≠ n ∧ i.val ≠ j.val + 1 → 
        (mat.get i).get j = (0 : Float))
    ⌝⦄ := by
  sorry
-- </vc-theorems>