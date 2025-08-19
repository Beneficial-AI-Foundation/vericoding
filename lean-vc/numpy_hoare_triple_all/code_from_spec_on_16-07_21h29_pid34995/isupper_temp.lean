import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def stringIsUpper (s : String) : Bool :=
  let chars := s.toList
  chars.length > 0 ∧ 
  (∃ c ∈ chars, c.isAlpha) ∧
  (∀ c ∈ chars, c.isAlpha → c.isUpper)

/-- Checks if all cased characters in each string are uppercase and there is at least one character -/
def isupper {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  return ⟨Array.map stringIsUpper a.toArray, by simp [Array.size_map]⟩

/-- Specification: isupper returns true for each element if all cased characters 
    in the string are uppercase and there is at least one character, false otherwise.
    Mathematical properties:
    1. Empty strings return false
    2. Strings with no cased characters return false  
    3. Strings with mixed case return false
    4. Strings with all cased characters uppercase return true -/
theorem isupper_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isupper a
    ⦃⇓result => ⌜∀ i : Fin n, 
                   let s := a.get i
                   let chars := s.toList
                   result.get i = (chars.length > 0 ∧ 
                                  (∃ c ∈ chars, c.isAlpha) ∧
                                  (∀ c ∈ chars, c.isAlpha → c.isUpper))⌝⦄ := by
  unfold isupper
  simp
  intro i
  simp [Vector.get, stringIsUpper]