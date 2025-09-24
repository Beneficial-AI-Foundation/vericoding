-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermsub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : 
    Id (Vector Float (max n m)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermsub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermsub c1 c2
    ⦃⇓result => ⌜
      -- For indices within both arrays, result is the difference
      (∀ i : Nat, i < min n m → 
        result.get ⟨i, sorry⟩ = c1.get ⟨i, sorry⟩ - c2.get ⟨i, sorry⟩) ∧
      -- For indices beyond c2's length (when n > m), result equals c1
      (n > m → ∀ i : Nat, m ≤ i ∧ i < n → 
        result.get ⟨i, sorry⟩ = c1.get ⟨i, sorry⟩) ∧
      -- For indices beyond c1's length (when m > n), result equals negation of c2
      (m > n → ∀ i : Nat, n ≤ i ∧ i < m → 
        result.get ⟨i, sorry⟩ = -c2.get ⟨i, sorry⟩)
    ⌝⦄ := by
  sorry
-- </vc-theorems>