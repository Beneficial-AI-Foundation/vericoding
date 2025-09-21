-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermevander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermevander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    hermevander x deg
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- First column is all ones (He_0(x) = 1)
      (result.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1 ∧

      -- Second column equals x when deg > 0 (He_1(x) = x)
      (deg > 0 → ∃ h : 1 < deg + 1, (result.get i).get ⟨1, h⟩ = x.get i) ∧

      -- For j ≥ 2: He_j(x) = x * He_{j-1}(x) - (j-1) * He_{j-2}(x)
      (∀ j : Fin (deg + 1), j.val ≥ 2 → 
        ∃ (h1 : j.val - 1 < deg + 1) (h2 : j.val - 2 < deg + 1),
        (result.get i).get j = 
          x.get i * (result.get i).get ⟨j.val - 1, h1⟩ - 
          (Float.ofNat (j.val - 1)) * (result.get i).get ⟨j.val - 2, h2⟩)⌝⦄ := by
  sorry
-- </vc-theorems>