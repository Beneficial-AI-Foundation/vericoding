import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.rstrip",
  "category": "String operations",
  "description": "For each element in a, return a copy with the trailing characters removed",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rstrip.html",
  "doc": "For each element in \`a\`, return a copy with the trailing characters removed.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nchars : array_like with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The characters to be removed. If None, whitespace characters are removed.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def rstrip(a, chars=None):\n    \"\"\"\n    For each element in \`a\`, return a copy with the trailing characters\n    removed.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    chars : array_like with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The \`\`chars\`\` argument is a string specifying the set of\n        characters to be removed. If \`\`None\`\`, the \`\`chars\`\`\n        argument defaults to removing whitespace. The \`\`chars\`\` argument\n        is not a prefix or suffix; rather, all combinations of its\n        values are stripped.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.rstrip\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', 'abBABba'], dtype='S7'); c\n    array([b'aAaAaA', b'abBABba'],\n          dtype='|S7')\n    >>> np.strings.rstrip(c, b'a')\n    array([b'aAaAaA', b'abBABb'],\n          dtype='|S7')\n    >>> np.strings.rstrip(c, b'A')\n    array([b'aAaAa', b'abBABba'],\n          dtype='|S7')\n\n    \"\"\"\n    if chars is None:\n        return _rstrip_whitespace_ufunc(a)\n    return _rstrip_chars_ufunc(a, chars)"
}
-/

/-- For each element in a vector, return a copy with the trailing characters removed. -/
def rstrip {n : Nat} (a : Vector String n) (chars : Option String) : Id (Vector String n) :=
  sorry

/-- Specification: numpy.strings.rstrip removes trailing characters from each string in the vector.
    
    rstrip removes trailing characters from the end of each string. If chars is None, 
    whitespace characters are removed. If chars is provided, any combination of those 
    characters is removed from the end.
    
    Mathematical Properties:
    1. Element-wise transformation: Each string is processed independently
    2. Trailing character removal: Only characters at the end are removed
    3. Maximal stripping: Remove as many trailing characters as possible
    4. Character set filtering: Only characters in the specified set are removed
    5. Whitespace default: When chars is None, whitespace characters are removed
    
    From NumPy documentation:
    - Parameters: a (array_like) - Input array with string dtype
                  chars (optional) - Characters to remove, whitespace if None
    - Returns: out (ndarray) - Output array with trailing characters removed
-/
theorem rstrip_spec {n : Nat} (a : Vector String n) (chars : Option String) :
    ⦃⌜True⌝⦄
    rstrip a chars
    ⦃⇓result => ⌜∀ i : Fin n, 
      let original := a.get i
      let stripped := result.get i
      -- Case 1: When chars is None, use trimRight (removes whitespace)
      (chars.isNone → stripped = original.trimRight) ∧
      -- Case 2: When chars is provided, remove characters from that set
      (chars.isSome → 
        ∃ suffix : String, 
          -- The result is the original string with the suffix removed
          (original = stripped ++ suffix) ∧
          -- The suffix consists only of characters from the chars set
          (∀ c : Char, c ∈ suffix.toList → c ∈ chars.get!.toList) ∧
          -- Maximal stripping: result doesn't end with any character from chars set
          (stripped = "" ∨ 
           ∀ c : Char, c ∈ chars.get!.toList → 
             stripped.back ≠ c) ∧
          -- Length constraint: result is never longer than original
          (stripped.length ≤ original.length))⌝⦄ := by
  sorry
