-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def loadtxt {rows cols : Nat} (filename : String) (delimiter : String := " ") 
    (skiprows : Nat := 0) : Id (Vector (Vector Float cols) rows) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem loadtxt_spec {rows cols : Nat} (filename : String) (delimiter : String := " ") 
    (skiprows : Nat := 0) 
    (h_rectangular : rows > 0 ∧ cols > 0) :
    ⦃⌜rows > 0 ∧ cols > 0 ∧ filename.length > 0⌝⦄
    loadtxt filename delimiter skiprows
    ⦃⇓result => ⌜
      -- Each element is finite (no NaN or infinite values for valid numeric input)
      (∀ i : Fin rows, ∀ j : Fin cols, (result.get i).get j |>.isFinite) ∧
      -- Parsing preserves numeric relationships for well-formed input
      (∀ i : Fin rows, ∀ j : Fin cols, 
        let val := (result.get i).get j
        val |>.isFinite → (val ≥ -1e308 ∧ val ≤ 1e308))⌝⦄ := by
  sorry
-- </vc-theorems>