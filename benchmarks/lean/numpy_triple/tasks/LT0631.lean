-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeat_string (s : String) (n : Int) : String :=
  if n ≤ 0 then "" else
  let rec aux (count : Nat) (acc : String) : String :=
    if count = 0 then acc
    else aux (count - 1) (s ++ acc)
  aux n.natAbs ""
  
def multiply {n : Nat} (a : Vector String n) (i : Vector Int n) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_spec {n : Nat} (a : Vector String n) (i : Vector Int n) :
    ⦃⌜True⌝⦄
    multiply a i
    ⦃⇓result => ⌜-- Core property: Element-wise string repetition
                 (∀ j : Fin n, result.get j = repeat_string (a.get j) (i.get j)) ∧
                 -- Zero/negative repetition property: Always yields empty string
                 (∀ j : Fin n, i.get j ≤ 0 → result.get j = "") ∧
                 -- Identity property: Multiplying by 1 yields the original string
                 (∀ j : Fin n, i.get j = 1 → result.get j = a.get j) ∧
                 -- Zero property: Multiplying by 0 yields empty string
                 (∀ j : Fin n, i.get j = 0 → result.get j = "") ∧
                 -- Empty string property: Empty strings remain empty regardless of repetition
                 (∀ j : Fin n, a.get j = "" → result.get j = "")⌝⦄ := by
  sorry
-- </vc-theorems>