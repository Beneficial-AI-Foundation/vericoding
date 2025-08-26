import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.count",
  "category": "String information",
  "description": "Returns an array with the number of non-overlapping occurrences of substring sub in the range [start, end]",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.count.html",
  "doc": "Returns an array with the number of non-overlapping occurrences of substring \`sub\` in the range [\`start\`, \`end\`].\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    The substring to search for.\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints",
  "code": "def count(a, sub, start=0, end=None):\n    \"\"\"\n    Returns an array with the number of non-overlapping occurrences of\n    substring \`\`sub\`\` in the range [\`\`start\`\`, \`\`end\`\`].\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        The substring to search for.\n\n    start, end : array_like, with any integer dtype, optional\n        The range to look in, interpreted as slice notation.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints\n\n    See Also\n    --------\n    str.count\n\n    Examples\n    --------\n    >>> c = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.count(c, 'A')\n    array([3, 1, 1])\n    >>> np.strings.count(c, 'aA')\n    array([3, 1, 0])\n    >>> np.strings.count(c, 'A', start=1, end=4)\n    array([2, 1, 0])\n    >>> np.strings.count(c, 'A', start=1, end=3)\n    array([1, 0, 0])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _count_ufunc(a, sub, start, end)"
}
-/

/-- numpy.strings.count: Returns an array with the number of non-overlapping occurrences 
    of substring sub in the range [start, end] for each element.

    For each string in the input array, counts how many times the substring appears
    without overlapping matches within the specified range. The search is performed
    within the range [start, end) where start and end are character indices.
-/
def count {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry

/-- Specification: numpy.strings.count returns the number of non-overlapping occurrences 
    of substring within the specified range for each element.
    
    Preconditions:
    - start ≤ end for all elements (valid range)
    - start and end indices are valid (within string bounds)
    - substring is not empty for all elements (to avoid infinite loops)
    
    Postconditions:
    - Result is non-negative for all elements
    - For each element, the count represents non-overlapping occurrences of substring
    - If substring is longer than search range, count is 0
    - The count is maximal (greedy non-overlapping matching)
-/
theorem count_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n)
    (h_range : ∀ i : Fin n, start.get i ≤ endPos.get i) 
    (h_bounds_start : ∀ i : Fin n, 0 ≤ start.get i ∧ start.get i ≤ (a.get i).length) 
    (h_bounds_end : ∀ i : Fin n, 0 ≤ endPos.get i ∧ endPos.get i ≤ (a.get i).length) 
    (h_nonempty : ∀ i : Fin n, sub.get i ≠ "") :
    ⦃⌜∀ i : Fin n, start.get i ≤ endPos.get i ∧ 
                   0 ≤ start.get i ∧ start.get i ≤ (a.get i).length ∧
                   0 ≤ endPos.get i ∧ endPos.get i ≤ (a.get i).length ∧ 
                   sub.get i ≠ ""⌝⦄
    count a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Result is non-negative
      result.get i ≥ 0 ∧
      -- If substring is empty, count is 0 (handled by precondition)
      -- If substring is longer than search range, count is 0
      ((sub.get i).length > Int.natAbs (endPos.get i - start.get i) → result.get i = 0) ∧
      -- The count represents the maximum number of non-overlapping occurrences
      (∃ positions : List Nat,
        -- All positions are valid and within the specified range
        (∀ p ∈ positions, 
          Int.natAbs (start.get i) ≤ p ∧ 
          p + (sub.get i).length ≤ Int.natAbs (endPos.get i) ∧
          p + (sub.get i).length ≤ (a.get i).length ∧
          -- The substring matches at this position (simplified check)
          ((a.get i).drop p).take (sub.get i).length = sub.get i) ∧
        -- Positions are sorted and non-overlapping
        (positions.Pairwise (· ≤ ·)) ∧
        (∀ j k : Nat, j < k → j < positions.length → k < positions.length →
          positions[j]! + (sub.get i).length ≤ positions[k]!) ∧
        -- The result equals the number of positions found
        result.get i = positions.length ∧
        -- This is the maximum possible count (optimality)
        (∀ other_positions : List Nat,
          (∀ p ∈ other_positions, 
            Int.natAbs (start.get i) ≤ p ∧ 
            p + (sub.get i).length ≤ Int.natAbs (endPos.get i) ∧
            p + (sub.get i).length ≤ (a.get i).length ∧
            ((a.get i).drop p).take (sub.get i).length = sub.get i) ∧
          (other_positions.Pairwise (· ≤ ·)) ∧
          (∀ j k : Nat, j < k → j < other_positions.length → k < other_positions.length →
            other_positions[j]! + (sub.get i).length ≤ other_positions[k]!) →
          other_positions.length ≤ positions.length))
    ⌝⦄ := by
  sorry