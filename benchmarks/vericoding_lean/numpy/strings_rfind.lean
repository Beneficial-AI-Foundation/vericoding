import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.rfind",
  "category": "String information",
  "description": "For each element, return the highest index in the string where substring sub is found, such that sub is contained within [start, end]",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rfind.html",
  "doc": "For each element, return the highest index in the string where substring \`sub\` is found, such that \`sub\` is contained within [\`start\`, \`end\`].\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    The substring to search for.\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints. Returns -1 if \`sub\` is not found.",
  "code": "def rfind(a, sub, start=0, end=None):\n    \"\"\"\n    For each element, return the highest index in the string where\n    substring \`\`sub\`\` is found, such that \`\`sub\`\` is contained within\n    [\`\`start\`\`, \`\`end\`\`].\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        The substring to search for.\n\n    start, end : array_like, with any integer dtype, optional\n        The range to look in, interpreted as slice notation.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints.  Returns -1 if \`\`sub\`\` is not found.\n\n    See Also\n    --------\n    str.rfind\n\n    Examples\n    --------\n    >>> a = np.array([\"Computer Science\"])\n    >>> np.strings.rfind(a, \"Science\", start=0, end=None)\n    array([9])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _rfind_ufunc(a, sub, start, end)"
}
-/

/-- For each element, return the highest index in the string where substring is found -/
def rfind {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: rfind returns the highest index where substring is found within range, or -1 if not found -/
theorem rfind_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 0 ≤ start.get i ∧ start.get i ≤ endPos.get i⌝⦄
    rfind a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Basic range constraint: result is -1 or within string bounds
      (result.get i = -1 ∨ (0 ≤ result.get i ∧ result.get i < (a.get i).length)) ∧
      -- If result is -1, no occurrence of substring within the specified range
      (result.get i = -1 → 
        ∀ j : Nat, start.get i ≤ j ∧ j + (sub.get i).length ≤ Int.natAbs (endPos.get i) + 1 ∧ 
                   j + (sub.get i).length ≤ (a.get i).length → 
          ¬String.startsWith ((a.get i).drop j) (sub.get i)) ∧
      -- If result is non-negative, it's the rightmost valid occurrence
      (result.get i ≥ 0 → 
        -- The result is within the search range
        start.get i ≤ result.get i ∧ 
        result.get i + (sub.get i).length ≤ endPos.get i + 1 ∧
        -- The substring matches at this position
        String.startsWith ((a.get i).drop (Int.natAbs (result.get i))) (sub.get i) ∧
        -- This is the rightmost occurrence within the range
        (∀ j : Int, result.get i < j ∧ j + (sub.get i).length ≤ endPos.get i + 1 ∧ 
                    start.get i ≤ j ∧ j + (sub.get i).length ≤ (a.get i).length → 
          ¬String.startsWith ((a.get i).drop (Int.natAbs j)) (sub.get i)))⌝⦄ := by
  sorry
