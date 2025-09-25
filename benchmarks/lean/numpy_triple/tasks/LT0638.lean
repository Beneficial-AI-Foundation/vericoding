-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rpartition {n : Nat} (a : Vector String n) (sep : String) : Id (Vector String n × Vector String n × Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rpartition_spec {n : Nat} (a : Vector String n) (sep : String) :
    ⦃⌜True⌝⦄
    rpartition a sep
    ⦃⇓result => ⌜let (before, separator, after) := result
                 ∀ i : Fin n, 
                   let original := a.get i
                   let before_i := before.get i
                   let sep_i := separator.get i
                   let after_i := after.get i
                   -- Partition property: reconstructs original string
                   before_i ++ sep_i ++ after_i = original ∧
                   -- Separator correctness: either the separator or empty string
                   (sep_i = sep ∨ sep_i = "") ∧
                   -- If separator is found, the separator part matches
                   (sep_i = sep → sep_i = sep) ∧
                   -- If separator is not found, first two parts are empty and after contains whole string
                   (sep_i = "" → before_i = "" ∧ after_i = original)⌝⦄ := by
  sorry
-- </vc-theorems>