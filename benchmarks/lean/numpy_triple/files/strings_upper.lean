/- 
{
  "name": "numpy.strings.upper",
  "category": "String transformation",
  "description": "Return an array with the elements converted to uppercase",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.upper.html",
  "doc": "Return an array with the elements converted to uppercase.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
}
-/

/-  numpy.strings.upper: Return an array with the elements converted to uppercase.

    Converts each string element in the input vector to uppercase. This transformation
    applies to all alphabetic characters while preserving non-alphabetic characters
    (digits, punctuation, whitespace) unchanged.

    The function preserves the shape of the input array and handles empty strings
    appropriately by returning them unchanged.

    From NumPy documentation:
    - Parameters: a (array_like) - Input array with string dtype
    - Returns: out (ndarray) - Output array with elements converted to uppercase

    Mathematical Properties:
    1. Element-wise transformation: result[i] = upper(a[i]) for all i
    2. Length preservation: result[i].length = a[i].length for all i
    3. Case transformation: lowercase letters become uppercase, others unchanged
    4. Idempotent: upper(upper(x)) = upper(x)
    5. Preserves vector length: result.size = a.size
-/

/-  Specification: numpy.strings.upper returns a vector where each string element
    is converted to uppercase.

    Mathematical Properties:
    1. Element-wise correctness: Each element is correctly converted to uppercase
    2. Length preservation: Each transformed string has the same length as the original
    3. Case transformation: Lowercase letters become uppercase, others unchanged
    4. Idempotent property: Applying upper twice gives the same result as applying it once
    5. Empty string handling: Empty strings remain empty
    6. Character-level correctness: Each character is correctly transformed

    Precondition: True (no special preconditions for uppercase conversion)
    Postcondition: For all indices i, result[i] is the uppercase version of a[i]
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def upper {n : Nat} (a : Vector String n) : Id (Vector String n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem upper_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    upper a
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches Lean's built-in toUpper
      (result = original.toUpper) ∧
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character-level transformation: each character is correctly converted
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          result.get? ⟨j⟩ = some origChar.toUpper) ∧
      -- Idempotent property: applying upper twice gives same result as once
      (result.toUpper = result) ∧
      -- Case preservation: non-alphabetic characters remain unchanged
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (¬origChar.isAlpha → result.get? ⟨j⟩ = some origChar)) ∧
      -- Alphabetic transformation: lowercase letters become uppercase
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (origChar.isLower → result.get? ⟨j⟩ = some origChar.toUpper))⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
