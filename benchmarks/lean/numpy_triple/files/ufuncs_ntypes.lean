import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ntypes {n : Nat} (ufunc_type_combinations : Vector String n) : Id Nat :=
  sorry

theorem ntypes_spec {n : Nat} (ufunc_type_combinations : Vector String (n + 1)) :
    ⦃⌜True⌝⦄
    ntypes ufunc_type_combinations
    ⦃⇓result => ⌜result = n + 1 ∧ result > 0⌝⦄ := by
  sorry
