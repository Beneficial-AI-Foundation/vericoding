import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def loadtxt {n : Nat} (fname : String) (skiprows : Nat := 0) : Id (Vector Float n) :=
  sorry

theorem loadtxt_spec {n : Nat} (fname : String) (skiprows : Nat) 
    (h_fname_valid : fname.length > 0) :
    ⦃⌜fname.length > 0 ∧ skiprows ≥ 0⌝⦄
    loadtxt fname skiprows
    ⦃⇓result => ⌜result.size = n ∧ 
                 (∀ i : Fin n, ∃ v : Float, result.get i = v ∧ 
                  -- The value is a properly parsed float from the file
                  True)⌝⦄ := by
  sorry
