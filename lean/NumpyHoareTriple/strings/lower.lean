import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.lower",
  "category": "String transformation",
  "description": "Return an array with the elements converted to lowercase",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.lower.html",
  "doc": "Return an array with the elements of \`a\` converted to lowercase.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type\n\nExamples\n--------\n>>> np.strings.lower(['HELLO', 'WORLD'])\narray(['hello', 'world'], dtype='<U5')",
  "code": "def lower(a):\n    \"\"\"\n    Return an array with the elements converted to lowercase.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.lower\n\n    Examples\n    --------\n    >>> c = np.array(['A1B C', '1BCA', 'BCA1']); c\n    array(['A1B C', '1BCA', 'BCA1'], dtype='<U5')\n    >>> np.strings.lower(c)\n    array(['a1b c', '1bca', 'bca1'], dtype='<U5')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _lower_ufunc(a)"
}
-/

/-- numpy.strings.lower: Return an array with the elements converted to lowercase.

    Converts each string element in the input vector to lowercase. This transformation
    applies to all alphabetic characters while preserving non-alphabetic characters
    (digits, punctuation, whitespace) unchanged.

    The function preserves the shape of the input array and handles empty strings
    appropriately by returning them unchanged.

    From NumPy documentation:
    - Parameters: a (array_like) - Input array with string dtype
    - Returns: out (ndarray) - Output array with elements converted to lowercase

    Mathematical Properties:
    1. Element-wise transformation: result[i] = lower(a[i]) for all i
    2. Length preservation: result[i].length = a[i].length for all i
    3. Case transformation: uppercase letters become lowercase, others unchanged
    4. Idempotent: lower(lower(x)) = lower(x)
    5. Preserves vector length: result.size = a.size
-/
def lower {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  sorry

/-- Specification: numpy.strings.lower returns a vector where each string element
    is converted to lowercase.

    Mathematical Properties:
    1. Element-wise correctness: Each element is correctly converted to lowercase
    2. Length preservation: Each transformed string has the same length as the original
    3. Case transformation: Uppercase letters become lowercase, others unchanged
    4. Idempotent property: Applying lower twice gives the same result as applying it once
    5. Empty string handling: Empty strings remain empty
    6. Character-level correctness: Each character is correctly transformed

    Precondition: True (no special preconditions for lowercase conversion)
    Postcondition: For all indices i, result[i] is the lowercase version of a[i]
-/
theorem lower_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    lower a
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches Lean's built-in toLower
      (result = original.toLower) ∧
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character-level transformation: each character is correctly converted
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          result.get? ⟨j⟩ = some origChar.toLower) ∧
      -- Idempotent property: applying lower twice gives same result as once
      (result.toLower = result) ∧
      -- Case preservation: non-alphabetic characters remain unchanged
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (¬origChar.isAlpha → result.get? ⟨j⟩ = some origChar)) ∧
      -- Alphabetic transformation: uppercase letters become lowercase
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (origChar.isUpper → result.get? ⟨j⟩ = some origChar.toLower))⌝⦄ := by
  sorry