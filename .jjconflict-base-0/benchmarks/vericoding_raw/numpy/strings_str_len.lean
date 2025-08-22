import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.str_len",
  "category": "String information",
  "description": "Returns the length of each element",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.str_len.html",
  "doc": "Returns the length of each element.\n\nFor byte strings, this is the number of bytes. For Unicode strings, this is the number of Unicode code points.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of ints",
  "code": "def str_len(a):\n    \"\"\"\n    Returns the length of each element.\n\n    For byte strings, this is the number of bytes. For Unicode\n    strings, this is the number of Unicode code points.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints\n\n    See Also\n    --------\n    len\n\n    Examples\n    --------\n    >>> a = np.array(['Grace Hopper Conference', 'Open Source Day'])\n    >>> np.strings.str_len(a)\n    array([23, 15])\n    >>> a = np.array([u'Р', u'о'])\n    >>> np.strings.str_len(a)\n    array([1, 1])\n    >>> a = np.array([['hello', 'world'], ['val', ''], [u'Р', u'о']])\n    >>> np.strings.str_len(a)\n    array([[5, 5],\n           [3, 0],\n           [1, 1]])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _str_len_ufunc(a)"
}
-/

/-- Returns the length of each string element in the vector.
    For Unicode strings, this counts the number of Unicode code points. -/
def str_len {n : Nat} (a : Vector String n) : Id (Vector Nat n) :=
  sorry

/-- Specification: str_len returns the length (number of Unicode code points) of each string element.
    
    Preconditions: None (str_len is defined for all strings)
    
    Postconditions:
    - The result vector has the same size as the input vector
    - Each element in the result corresponds to the length of the corresponding input string
    - Length is always non-negative (natural number)
    - Empty strings have length 0
    - Length is measured in Unicode code points for Unicode strings
-/
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
  sorry
