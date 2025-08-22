import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.strings.capitalize",
  "category": "String transformation",
  "description": "Return a copy of a with only the first character of each element capitalized",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.capitalize.html",
  "doc": "Return a copy of \`a\` with only the first character of each element capitalized.\n\nFor byte strings, this method is locale-dependent.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array of strings\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types\n\nExamples\n--------\n>>> np.strings.capitalize(['hello', 'world'])\narray(['Hello', 'World'], dtype='<U5')",
  "code": "def capitalize(a):\n    \"\"\"\n    Return a copy of \`\`a\`\` with only the first character of each element\n    capitalized.\n\n    For byte strings, this method is locale-dependent.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array of strings\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.capitalize\n\n    Examples\n    --------\n    >>> c = np.array(['a1b2','1b2a','b2a1','2a1b'],'S4'); c\n    array([b'a1b2', b'1b2a', b'b2a1', b'2a1b'],\n          dtype='|S4')\n    >>> np.strings.capitalize(c)\n    array([b'A1b2', b'1b2a', b'B2a1', b'2a1b'],\n          dtype='|S4')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _capitalize_ufunc(a)"
}
-/

open Std.Do

/-- Return a copy of a with only the first character of each element capitalized -/
def capitalize {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  sorry

/-- Specification: capitalize returns a vector where each string has only its first character capitalized -/
theorem capitalize_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    capitalize a
    ⦃⇓r => ⌜∀ i : Fin n,
      let original := a.get i
      let result := r.get i
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Core property: the result is the capitalized version of the original
      (result = original.capitalize) ∧
      -- Idempotence property: capitalizing a capitalized string doesn't change it
      (result.capitalize = result) ∧
      -- Sanity check: applying capitalize to empty string gives empty string
      (original = "" → result = "") ∧
      -- Mathematical property: the operation is deterministic
      (result = original.capitalize)⌝⦄ := by
  sorry
