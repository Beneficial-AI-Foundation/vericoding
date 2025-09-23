-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def less {n : Nat} (x1 x2 : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem less_spec {n : Nat} (x1 x2 : Vector String n) :
    ⦃⌜True⌝⦄
    less x1 x2
    ⦃⇓result => ⌜-- Core property: result[i] = (x1[i] < x2[i]) for all indices
                 (∀ i : Fin n, result.get i = (x1.get i < x2.get i)) ∧
                 -- Asymmetry: if x1[i] < x2[i], then NOT (x2[i] < x1[i])
                 (∀ i : Fin n, result.get i = true → ¬(x2.get i < x1.get i)) ∧
                 -- Irreflexivity: no string is less than itself
                 (∀ i : Fin n, x1.get i = x2.get i → result.get i = false) ∧
                 -- Transitivity property: if x1[i] < x2[i] and we have a third string x3[i], transitivity holds
                 (∀ i : Fin n, result.get i = true → ∀ s : String, x2.get i < s → x1.get i < s) ∧
                 -- Decidability: result is always boolean (true or false)
                 (∀ i : Fin n, result.get i = true ∨ result.get i = false) ∧
                 -- Empty string property: empty string is less than any non-empty string
                 (∀ i : Fin n, x1.get i = "" → x2.get i ≠ "" → result.get i = true) ∧
                 -- Non-empty string property: non-empty string is not less than empty string
                 (∀ i : Fin n, x1.get i ≠ "" → x2.get i = "" → result.get i = false) ∧
                 -- Length invariant: result has same length as input vectors  
                 (result.toList.length = n) ∧
                 -- Consistency with String's built-in less-than operator
                 (∀ i : Fin n, result.get i = true ↔ x1.get i < x2.get i) ∧
                 -- Prefix property: if s1 is a proper prefix of s2, then s1 < s2
                 (∀ i : Fin n, (x1.get i).isPrefixOf (x2.get i) → x1.get i ≠ x2.get i → result.get i = true) ∧
                 -- Strict ordering: if result[i] is true, then x1[i] and x2[i] are different
                 (∀ i : Fin n, result.get i = true → x1.get i ≠ x2.get i) ∧
                 -- Totality of comparison: for any two strings, exactly one of <, =, > holds
                 (∀ i : Fin n, result.get i = true ∨ x1.get i = x2.get i ∨ x2.get i < x1.get i)⌝⦄ := by
  sorry
-- </vc-theorems>