import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.rsplit",
  "category": "String operations",
  "description": "For each element in a, return a list of the words in the string, using sep as the delimiter string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rsplit.html",
  "doc": "For each element in \`a\`, return a list of the words in the string, using \`sep\` as the delimiter string.\n\nSplits from the right.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    If \`sep\` is not specified or None, any whitespace string is a separator.\nmaxsplit : array_like, with any integer dtype, optional\n    If \`maxsplit\` is given, at most \`maxsplit\` splits are done.\n\nReturns\n-------\nout : ndarray\n    Output array of objects",
  "code": "def rsplit(a, sep=None, maxsplit=None):\n    \"\"\"\n    For each element in \`\`a\`\`, return a list of the words in the\n    string, using \`\`sep\`\` as the delimiter string.\n\n    Splits from the right.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sep : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        If \`\`sep\`\` is not specified or \`\`None\`\`, any whitespace string\n        is a separator.\n\n    maxsplit : array_like, with any integer dtype\n        If \`\`maxsplit\`\` is given, at most \`\`maxsplit\`\` splits are done.\n\n    Returns\n    -------\n    out : ndarray\n        Array of list objects\n\n    See Also\n    --------\n    str.rsplit, split\n\n    Examples\n    --------\n    >>> a = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.rsplit(a, 'A')\n    array([list(['a', 'a', 'a', '']),\n           list(['  a', '  ']),\n           list(['abB', 'Bba'])], dtype=object)\n\n    \"\"\"\n    if not np.isscalar(a):\n        a = np.asanyarray(a)\n    if a.dtype.char == \"T\":\n        return _rsplit(a, sep, maxsplit)\n    return _to_bytes_or_str_array(_rsplit(_to_string_dtype_array(a), sep, maxsplit))"
}
-/

/-- For each element in a vector, return a list of the words in the string, using sep as the delimiter string.
    Splits from the right, meaning that splits are made from the right side of the string. -/
def rsplit {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Nat) : Id (Vector (List String) n) :=
  sorry

/-- Specification: rsplit splits each string in the vector from the right using the given separator.
    The resulting vector contains lists of strings where each list represents the split parts
    of the corresponding input string. -/
theorem rsplit_spec {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Nat) :
    ⦃⌜sep ≠ ""⌝⦄ 
    rsplit a sep maxsplit
    ⦃⇓result => ⌜
      -- Each element in result corresponds to an element in input a
      (∀ i : Fin n, (result.get i).length > 0) ∧
      -- When maxsplit is 0, no splitting occurs
      (maxsplit = 0 → ∀ i : Fin n, result.get i = [a.get i]) ∧
      -- The number of splits is at most maxsplit for each string
      (∀ i : Fin n, (result.get i).length ≤ maxsplit + 1) ∧
      -- When joined back together with separator, we get the original string
      (∀ i : Fin n, maxsplit = 0 → String.intercalate sep (result.get i) = a.get i) ∧
      -- If separator doesn't exist in string, result is single element list
      (∀ i : Fin n, (a.get i).splitOn sep = [a.get i] → result.get i = [a.get i]) ∧
      -- Empty strings split to empty list or single empty string
      (∀ i : Fin n, a.get i = "" → result.get i = [""]) ∧
      -- The split respects the right-to-left order (last occurrences split first)
      (∀ i : Fin n, ∀ parts : List String, result.get i = parts → 
        parts.length > 1 → 
        String.intercalate sep parts = a.get i)⌝⦄ := by
  sorry