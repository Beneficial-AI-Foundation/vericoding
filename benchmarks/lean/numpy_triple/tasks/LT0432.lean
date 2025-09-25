-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def herm2poly {n : Nat} (c : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem herm2poly_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    herm2poly c
    ⦃⇓result => ⌜
      -- Sanity checks
      (n = 1 → result = c) ∧
      (n = 2 → result.get ⟨0, sorry⟩ = c.get ⟨0, sorry⟩ ∧ 
               result.get ⟨1, sorry⟩ = 2 * c.get ⟨1, sorry⟩) ∧
      -- Example from documentation
      (n = 4 ∧ c.get ⟨0, sorry⟩ = 1 ∧ c.get ⟨1, sorry⟩ = 2.75 ∧ 
       c.get ⟨2, sorry⟩ = 0.5 ∧ c.get ⟨3, sorry⟩ = 0.375 →
       result.get ⟨0, sorry⟩ = 0 ∧ result.get ⟨1, sorry⟩ = 1 ∧
       result.get ⟨2, sorry⟩ = 2 ∧ result.get ⟨3, sorry⟩ = 3) ∧
      -- Mathematical property: The transformation is invertible
      -- There exists poly2herm such that poly2herm(herm2poly(c)) = c
      (∃ poly2herm : Vector Float n → Vector Float n, 
        poly2herm result = c)
    ⌝⦄ := by
  sorry
-- </vc-theorems>