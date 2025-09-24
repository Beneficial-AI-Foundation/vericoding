-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermcompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_nonzero : c.get ⟨n + 1, by omega⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, by omega⟩ ≠ 0⌝⦄
    hermcompanion c
    ⦃⇓mat => ⌜
      -- The matrix has the correct diagonal structure
      (∀ k : Fin n, (mat.get ⟨k.val, by omega⟩).get ⟨k.val + 1, by omega⟩ = 
        Float.sqrt (0.5 * Float.ofNat (k.val + 1))) ∧
      (∀ k : Fin n, (mat.get ⟨k.val + 1, by omega⟩).get ⟨k.val, by omega⟩ = 
        Float.sqrt (0.5 * Float.ofNat (k.val + 1))) ∧
      -- All other entries except last column are zero
      (∀ i j : Fin (n + 1), 
        (i.val + 1 ≠ j.val ∧ j.val + 1 ≠ i.val ∧ j.val ≠ n) → 
        (mat.get i).get j = 0) ∧
      -- Last column has special scaling based on coefficients
      (∀ i : Fin (n + 1), 
        ∃ scale : Float, (mat.get i).get ⟨n, by omega⟩ = 
          if i.val + 1 = n ∨ i.val = n + 1 then
            Float.sqrt (0.5 * Float.ofNat n) - scale * c.get ⟨i.val, by omega⟩ / (2.0 * c.get ⟨n + 1, by omega⟩)
          else
            - scale * c.get ⟨i.val, by omega⟩ / (2.0 * c.get ⟨n + 1, by omega⟩))
    ⌝⦄ := by
  sorry
-- </vc-theorems>