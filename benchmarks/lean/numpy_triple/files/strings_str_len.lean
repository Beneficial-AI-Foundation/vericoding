/- 
{
  "name": "numpy.strings.str_len",
  "category": "String information",
  "description": "Returns the length of each element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.str_len.html",
  "doc": "Returns the length of each element.\n\nFor byte strings, this is the number of bytes. For Unicode strings, this is the number of Unicode code points.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of ints",
}
-/

/-  Returns the length of each string element in the vector.
    For Unicode strings, this counts the number of Unicode code points. -/

/-  Specification: str_len returns the length (number of Unicode code points) of each string element.
    
    Preconditions: None (str_len is defined for all strings)
    
    Postconditions:
    - The result vector has the same size as the input vector
    - Each element in the result corresponds to the length of the corresponding input string
    - Length is always non-negative (natural number)
    - Empty strings have length 0
    - Length is measured in Unicode code points for Unicode strings
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def str_len {n : Nat} (a : Vector String n) : Id (Vector Nat n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem str_len_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    str_len a
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Basic correctness: result contains the length of each string
      result.get i = (a.get i).length ∧
      -- Non-negativity: lengths are always non-negative (natural numbers)
      result.get i ≥ 0 ∧
      -- Empty string property: empty strings have length 0
      (a.get i = "" ↔ result.get i = 0) ∧
      -- Single character property: single characters have length 1
      (a.get i ≠ "" ∧ (a.get i).drop 1 = "" → result.get i = 1) ∧
      -- Monotonicity property: longer strings have lengths ≥ shorter prefixes
      (∀ k : Nat, k ≤ (a.get i).length → 
        ((a.get i).take k).length ≤ result.get i) ∧
      -- Deterministic property: same string always gives same length
      (∀ j : Fin n, a.get i = a.get j → result.get i = result.get j) ∧
      -- Concatenation property: length is additive for concatenation
      (∀ s1 s2 : String, a.get i = s1 ++ s2 → 
        result.get i = s1.length + s2.length)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
