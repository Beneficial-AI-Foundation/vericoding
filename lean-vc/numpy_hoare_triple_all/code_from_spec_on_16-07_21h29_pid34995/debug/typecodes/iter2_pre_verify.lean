import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Returns the type character codes for a given NumPy dtype category -/
def typecodes (category : String) : Id (Option String) :=
  match category with
  | "Character" => some "S1"
  | "Integer" => some "bhilqnp"
  | "UnsignedInteger" => some "BHILQNP"
  | "Float" => some "fdg"
  | "Complex" => some "FDG"
  | "AllInteger" => some "bBhHiIlLqQnNpP"
  | "AllFloat" => some "fdgFDG"
  | "Datetime" => some "Mm"
  | "All" => some "?bhilqnpBHILQNPfdgFDGSUVOMm"
  | _ => none

/-- Specification: typecodes returns the correct type character codes for each NumPy dtype category -/
theorem typecodes_spec (category : String) :
    ⦃⌜True⌝⦄
    typecodes category
    ⦃⇓result => ⌜
      (category = "Character" → result = some "S1") ∧
      (category = "Integer" → result = some "bhilqnp") ∧
      (category = "UnsignedInteger" → result = some "BHILQNP") ∧
      (category = "Float" → result = some "fdg") ∧
      (category = "Complex" → result = some "FDG") ∧
      (category = "AllInteger" → result = some "bBhHiIlLqQnNpP") ∧
      (category = "AllFloat" → result = some "fdgFDG") ∧
      (category = "Datetime" → result = some "Mm") ∧
      (category = "All" → result = some "?bhilqnpBHILQNPfdgFDGSUVOMm") ∧
      (category ∉ ["Character", "Integer", "UnsignedInteger", "Float", "Complex", "AllInteger", "AllFloat", "Datetime", "All"] → result = none)
    ⌝⦄ := by
  simp [typecodes]
  split
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp [List.mem_cons, List.mem_singleton]