import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.find",
  "category": "String information",
  "description": "For each element, return the lowest index in the string where substring sub is found",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.find.html",
  "doc": "For each element, return the lowest index in the string where substring \`sub\` is found, such that \`sub\` is contained in the range [\`start\`, \`end\`].\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints. Returns -1 if \`sub\` is not found.",
  "code": "def find(a, sub, start=0, end=None):\n    \"\"\"\n    For each element, return the lowest index in the string where\n    substring \`\`sub\`\` is found, such that \`\`sub\`\` is contained in the\n    range [\`\`start\`\`, \`\`end\`\`].\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        The substring to search for.\n\n    start, end : array_like, with any integer dtype, optional\n        The range to look in, interpreted as slice notation.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints.  Returns -1 if \`\`sub\`\` is not found.\n\n    See Also\n    --------\n    str.find\n\n    Examples\n    --------\n    >>> a = np.array([\"NumPy is a Python library\"])\n    >>> np.strings.find(a, \"Python\", start=0, end=None)\n    array([11])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _find_ufunc(a, sub, start, end)"
}
-/

/-- For each element, return the lowest index in the string where substring is found -/
def find {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: find returns the lowest index where substring is found within range, or -1 if not found -/
theorem find_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 0 ≤ start.get i ∧ start.get i ≤ endPos.get i ∧ endPos.get i < (a.get i).length⌝⦄
    find a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Case 1: substring not found (returns -1)
      (result.get i = -1 ↔ 
        ∀ pos : Nat, start.get i ≤ pos ∧ pos ≤ endPos.get i ∧ pos + (sub.get i).length ≤ (a.get i).length → 
          ¬(((a.get i).drop pos).take (sub.get i).length = sub.get i)) ∧
      -- Case 2: substring found (returns non-negative index)
      (result.get i ≥ 0 → 
        -- Result is within valid range
        start.get i ≤ result.get i ∧ 
        result.get i ≤ endPos.get i ∧
        result.get i + (sub.get i).length ≤ (a.get i).length ∧
        -- Substring actually found at this position
        ((a.get i).drop (Int.natAbs (result.get i))).take (sub.get i).length = sub.get i ∧
        -- This is the LOWEST index where substring is found (minimality property)
        (∀ pos : Nat, start.get i ≤ pos ∧ pos < Int.natAbs (result.get i) → 
          ¬(((a.get i).drop pos).take (sub.get i).length = sub.get i))) ∧
      -- Sanity check 1: empty substring is found at start position
      (sub.get i = "" → result.get i = start.get i) ∧
      -- Sanity check 2: substring longer than remaining string cannot be found
      (start.get i + (sub.get i).length > (a.get i).length → result.get i = -1) ∧
      -- Sanity check 3: if start > end, no substring can be found
      (start.get i > endPos.get i → result.get i = -1)⌝⦄ := by
  sorry
