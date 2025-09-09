import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def array2string {n : Nat} (arr : Vector Float n) (separator : String := " ") : Id String :=
  sorry

theorem array2string_spec {n : Nat} (arr : Vector Float n) (separator : String) :
    ⦃⌜True⌝⦄
    array2string arr separator
    ⦃⇓result => ⌜result ≠ "" ∧ result.startsWith "[" ∧ result.endsWith "]"⌝⦄ := by
  sorry
