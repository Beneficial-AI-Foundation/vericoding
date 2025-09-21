-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    legvander x deg
    ⦃⇓result => ⌜
      -- First column (L_0) is all ones
      (∀ i : Fin n, (result.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1) ∧
      -- Second column (L_1) equals x values when deg > 0
      (deg > 0 → ∀ i : Fin n, (result.get i).get ⟨1, sorry⟩ = x.get i) ∧
      -- Matrix has correct dimensions and well-defined values
      (∀ i : Fin n, ∀ j : Fin (deg + 1), ∃ val : Float, (result.get i).get j = val)
    ⌝⦄ := by
  sorry
-- </vc-theorems>