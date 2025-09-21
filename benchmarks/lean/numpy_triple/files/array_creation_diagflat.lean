-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagflat {n : Nat} (v : Vector Float n) : Id (Vector Float (n * n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagflat_spec {n : Nat} (v : Vector Float n) :
    ⦃⌜True⌝⦄
    diagflat v
    ⦃⇓result => ⌜
      -- Elements on the main diagonal are from the input vector
      (∀ i : Fin n, result.get ⟨i.val * n + i.val, sorry⟩ = v.get i) ∧
      -- All other elements are zero
      (∀ i j : Fin n, i ≠ j → result.get ⟨i.val * n + j.val, sorry⟩ = 0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>