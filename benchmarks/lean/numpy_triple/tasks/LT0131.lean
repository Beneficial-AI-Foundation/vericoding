-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- NumPy type character to precedence mapping based on the default typeset 'GDFgdf'
    Lower values indicate higher precedence (smaller/more restrictive types) -/
def typechar_precedence : Char → Nat
  | 'g' => 0  -- longdouble (most restrictive in numerical sense)
  | 'd' => 1  -- double
  | 'f' => 2  -- float
  | 'F' => 3  -- csingle (complex float)
  | 'D' => 4  -- cdouble (complex double)
  | 'G' => 5  -- clongdouble (complex long double)
  | _   => 6  -- other types (lowest precedence)
/-- Check if a type character is in the given typeset -/
def char_in_typeset {n : Nat} (c : Char) (typeset : Vector Char n) : Bool :=
  typeset.toList.contains c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mintypecode {n m : Nat} (typechars : Vector Char n) (typeset : Vector Char m) (default : Char) : Id Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mintypecode_spec {n m : Nat} (typechars : Vector Char n) (typeset : Vector Char m) (default : Char) 
    (h_typeset : typeset.toList = ['G', 'D', 'F', 'g', 'd', 'f']) :
    ⦃⌜typeset.toList = ['G', 'D', 'F', 'g', 'd', 'f']⌝⦄
    mintypecode typechars typeset default
    ⦃⇓result => ⌜
      -- Case 1: No input types in typeset - return default
      (∀ c ∈ typechars.toList, ¬(char_in_typeset c typeset) → result = default) ∧

      -- Case 2: Special rule - if both 'F' and 'd' are in intersection, return 'D'
      (∃ (intersection : List Char), 
        intersection = (typechars.toList.filter (fun c => char_in_typeset c typeset)) ∧
        intersection.length > 0 ∧
        ('F' ∈ intersection ∧ 'd' ∈ intersection → result = 'D')) ∧

      -- Case 3: Normal case - return minimum precedence type from intersection
      (∃ (intersection : List Char),
        intersection = (typechars.toList.filter (fun c => char_in_typeset c typeset)) ∧
        intersection.length > 0 ∧
        ¬('F' ∈ intersection ∧ 'd' ∈ intersection) →
        (result ∈ intersection ∧ 
         ∀ c ∈ intersection, typechar_precedence result ≤ typechar_precedence c)) ∧

      -- Validity: result is either from intersection or default
      (result ∈ (typechars.toList.filter (fun c => char_in_typeset c typeset)) ∨ 
       result = default) ∧

      -- Safety property: result can handle all input types
      (∀ c ∈ typechars.toList, char_in_typeset c typeset → 
        typechar_precedence result ≤ typechar_precedence c ∨ 
        (result = 'D' ∧ ('F' ∈ typechars.toList ∧ 'd' ∈ typechars.toList)))
    ⌝⦄ := by
  sorry
-- </vc-theorems>