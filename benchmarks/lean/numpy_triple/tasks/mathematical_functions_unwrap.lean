-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unwrap {n : Nat} (p : Vector Float n) (discont : Float := 3.141592653589793) (period : Float := 2 * 3.141592653589793) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unwrap_spec {n : Nat} (p : Vector Float n) (discont : Float := 3.141592653589793) (period : Float := 2 * 3.141592653589793) 
    (h_pos_discont : discont > 0) (h_pos_period : period > 0) :
    ⦃⌜discont > 0 ∧ period > 0⌝⦄
    unwrap p discont period
    ⦃⇓result => ⌜
      -- First element is unchanged (if array is non-empty)
      (∀ h : n > 0, result.get ⟨0, h⟩ = p.get ⟨0, h⟩) ∧
      -- For consecutive elements, differences are bounded by discont  
      (∀ i : Fin n, ∀ h_next : i.val + 1 < n,
        let idx_next : Fin n := ⟨i.val + 1, h_next⟩
        Float.abs (result.get idx_next - result.get i) ≤ discont) ∧
      -- Result differs from input by multiples of period
      (∀ i : Fin n, ∃ k : Float, result.get i = p.get i + k * period)
    ⌝⦄ := by
  sorry
-- </vc-theorems>