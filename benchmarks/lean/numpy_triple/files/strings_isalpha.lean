-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isalpha {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  a.map (fun s => s ≠ "" ∧ s.toList.all Char.isAlpha)
-- </vc-definitions>

-- <vc-theorems>
theorem isalpha_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isalpha a
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Core property: result matches the definition
      result.get i = (a.get i ≠ "" ∧ (a.get i).toList.all Char.isAlpha) ∧
      -- Sanity check: empty strings are always false
      (a.get i = "" → result.get i = false) ∧
      -- Sanity check: non-empty strings are true iff all chars are alphabetic
      (a.get i ≠ "" → (result.get i ↔ (a.get i).toList.all Char.isAlpha)) ∧
      -- Mathematical property: if result is true, then string is non-empty
      (result.get i = true → a.get i ≠ "") ∧
      -- Mathematical property: if result is true, then all chars are alphabetic
      (result.get i = true → (a.get i).toList.all Char.isAlpha) ∧
      -- Mathematical property: if string has non-alphabetic char, result is false
      (∃ c ∈ (a.get i).toList, ¬Char.isAlpha c → result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>