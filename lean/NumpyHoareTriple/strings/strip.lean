import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.strip",
  "category": "String operations",
  "description": "For each element in a, return a copy with the leading and trailing characters removed",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.strip.html",
  "doc": "For each element in \`a\`, return a copy with the leading and trailing characters removed.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nchars : array_like with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The characters to be removed. If None, whitespace characters are removed.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def strip(a, chars=None):\n    \"\"\"\n    For each element in \`a\`, return a copy with the leading and\n    trailing characters removed.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    chars : array_like with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The \`\`chars\`\` argument is a string specifying the set of\n        characters to be removed. If \`\`None\`\`, the \`\`chars\`\`\n        argument defaults to removing whitespace. The \`\`chars\`\` argument\n        is not a prefix or suffix; rather, all combinations of its\n        values are stripped.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.strip\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.strip(c)\n    array(['aAaAaA', 'aA', 'abBABba'], dtype='<U7')\n    >>> np.strings.strip(c, 'a')\n    array(['AaAaA', '  aA  ', 'bBABb'], dtype='<U7')\n    >>> np.strings.strip(c, 'A')\n    array(['aAaAa', '  aA  ', 'abBABba'], dtype='<U7')\n\n    \"\"\"\n    if chars is None:\n        return _strip_whitespace_ufunc(a)\n    return _strip_chars_ufunc(a, chars)"
}
-/

/-- numpy.strings.strip: For each element in a vector, return a copy with the leading and trailing characters removed.

    Removes both leading and trailing characters from each string element in the input vector.
    This is a combination of lstrip and rstrip operations. The behavior depends on the chars parameter:
    - If chars is None, whitespace characters are removed from both ends
    - If chars is provided, any combination of those characters is removed from both ends
    
    The function preserves the shape of the input array and handles empty strings
    appropriately by returning them unchanged.

    From NumPy documentation:
    - Parameters: a (array_like) - Input array with string dtype
                  chars (optional) - Characters to remove from both ends
    - Returns: out (ndarray) - Output array with leading and trailing characters removed

    Mathematical Properties:
    1. Element-wise transformation: result[i] = strip(a[i], chars) for all i
    2. Length preservation or reduction: result[i].length ≤ a[i].length for all i
    3. Substring property: result[i] is a substring of a[i] for all i
    4. Character set removal: only characters in chars are removed from both ends
    5. Preserves vector length: result.size = a.size
    6. Combination of lstrip and rstrip: strip(s) = rstrip(lstrip(s))
-/
def strip {n : Nat} (a : Vector String n) (chars : Option String) : Id (Vector String n) :=
  sorry

/-- Specification: numpy.strings.strip returns a vector where each string element
    has its leading and trailing characters removed according to the chars parameter.

    Mathematical Properties:
    1. Element-wise correctness: Each element is correctly processed for both leading and trailing character removal
    2. Length preservation or reduction: Each result string is no longer than the original
    3. Substring property: Each result is a substring of the original string
    4. Character set stripping: Only characters in chars are removed from both ends
    5. Whitespace default: When chars is None, whitespace characters are removed
    6. Maximal stripping: Remove as many characters as possible from both ends
    7. Empty string handling: Empty strings remain empty
    8. Middle preservation: Characters in the middle of the string are unchanged
    9. Composition property: strip combines lstrip and rstrip functionality
    10. Idempotent-like property: applying strip to result with same chars removes nothing

    Precondition: True (no special preconditions for strip)
    Postcondition: For all indices i, result[i] is a[i] with leading and trailing characters removed
-/
theorem strip_spec {n : Nat} (a : Vector String n) (chars : Option String) :
    ⦃⌜True⌝⦄
    strip a chars
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches expected behavior
      (chars.isNone → result = original.trim) ∧
      -- Length preservation or reduction: result is no longer than original
      (result.length ≤ original.length) ∧
      -- Substring property: result is a substring of original
      (∃ start : Nat, ∃ len : Nat, 
        start + len ≤ original.length ∧ 
        result = original.extract ⟨start⟩ ⟨start + len⟩) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character removal correctness: when chars is provided
      (chars.isSome →
        ∃ start : Nat, ∃ len : Nat,
        start + len ≤ original.length ∧ 
        result = original.extract ⟨start⟩ ⟨start + len⟩ ∧
        -- All stripped leading characters are in the chars set
        (∀ j : Nat, j < start → 
          ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
        -- All stripped trailing characters are in the chars set
        (∀ j : Nat, start + len < j → j < original.length →
          ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
        -- The first non-stripped character (if any) is not in chars
        (start < original.length → start + len > start →
          ∃ c : Char, original.get? ⟨start⟩ = some c ∧ c ∉ chars.get!.toList) ∧
        -- The last non-stripped character (if any) is not in chars
        (start + len > 0 → start + len ≤ original.length →
          ∃ c : Char, original.get? ⟨start + len - 1⟩ = some c ∧ c ∉ chars.get!.toList)) ∧
      -- Maximal stripping: result cannot have leading or trailing chars from the set removed
      (chars.isSome → 
        (result = "" ∨ 
         (∀ c : Char, c ∈ chars.get!.toList → 
           result.get? ⟨0⟩ ≠ some c ∧ result.back ≠ c))) ∧
      -- Composition property: strip is equivalent to rstrip(lstrip(...))
      (chars.isSome →
        ∃ intermediate : String,
        -- First apply lstrip
        (∃ k : Nat, k ≤ original.length ∧ 
         intermediate = original.drop k ∧
         (∀ j : Nat, j < k → 
           ∃ c : Char, original.get? ⟨j⟩ = some c ∧ c ∈ chars.get!.toList) ∧
         (k < original.length → 
           ∃ c : Char, original.get? ⟨k⟩ = some c ∧ c ∉ chars.get!.toList)) ∧
        -- Then apply rstrip to get final result
        (∃ suffix : String, 
          intermediate = result ++ suffix ∧
          (∀ c : Char, c ∈ suffix.toList → c ∈ chars.get!.toList) ∧
          (result = "" ∨ 
           ∀ c : Char, c ∈ chars.get!.toList → result.back ≠ c))) ∧
      -- Middle preservation: characters that remain are in the same order
      (∀ j k : Nat, j < k → k < result.length → 
        ∃ origJ origK : Nat, j < origJ → origJ < origK → origK < original.length →
          result.get? ⟨j⟩ = original.get? ⟨origJ⟩ ∧ 
          result.get? ⟨k⟩ = original.get? ⟨origK⟩)⌝⦄ := by
  sorry