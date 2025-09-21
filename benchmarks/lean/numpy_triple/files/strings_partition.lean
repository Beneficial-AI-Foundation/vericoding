-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def partition {n : Nat} (a : Vector String n) (sep : String) : Id (Vector String n × Vector String n × Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem partition_spec {n : Nat} (a : Vector String n) (sep : String) :
    ⦃⌜True⌝⦄
    partition a sep
    ⦃⇓result => ⌜let (before, separator, after) := result
                 ∀ i : Fin n, 
                   let original := a.get i
                   let before_i := before.get i
                   let sep_i := separator.get i
                   let after_i := after.get i
                   -- Fundamental partition property: parts reconstruct original string
                   before_i ++ sep_i ++ after_i = original ∧
                   -- Separator correctness: either the separator or empty string
                   (sep_i = sep ∨ sep_i = "") ∧
                   -- Case 1: Separator found - the separator part is exactly the separator
                   (sep_i = sep → sep_i = sep) ∧
                   -- Case 2: Separator not found - before contains whole string, others empty
                   (sep_i = "" → after_i = "" ∧ before_i = original) ∧
                   -- Length preservation: total length is preserved
                   original.length = before_i.length + sep_i.length + after_i.length⌝⦄ := by
  sorry
-- </vc-theorems>