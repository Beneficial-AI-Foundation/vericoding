-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def typename (char : String) : Id String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem typename_spec (char : String) :
    ⦃⌜True⌝⦄
    typename char
    ⦃⇓result => ⌜
      -- Known type code mappings from NumPy documentation
      (char = "S1" → result = "character") ∧
      (char = "?" → result = "bool") ∧
      (char = "B" → result = "unsigned char") ∧
      (char = "D" → result = "complex double precision") ∧
      (char = "G" → result = "complex long double precision") ∧
      (char = "F" → result = "complex single precision") ∧
      (char = "I" → result = "unsigned integer") ∧
      (char = "H" → result = "unsigned short") ∧
      (char = "L" → result = "unsigned long integer") ∧
      (char = "O" → result = "object") ∧
      (char = "Q" → result = "unsigned long long integer") ∧
      (char = "S" → result = "character") ∧
      (char = "U" → result = "unicode") ∧
      (char = "V" → result = "void") ∧
      (char = "b" → result = "signed char") ∧
      (char = "d" → result = "double precision") ∧
      (char = "g" → result = "long precision") ∧
      (char = "f" → result = "single precision") ∧
      (char = "i" → result = "integer") ∧
      (char = "h" → result = "short") ∧
      (char = "l" → result = "long integer") ∧
      (char = "q" → result = "long long integer") ∧
      -- For unknown type codes, the function should return some default description
      (char ∉ ["S1", "?", "B", "D", "G", "F", "I", "H", "L", "O", "Q", 
               "S", "U", "V", "b", "d", "g", "f", "i", "h", "l", "q"] → 
       result = "unknown type" ∨ result = char)
    ⌝⦄ := by
  sorry
-- </vc-theorems>