import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.endswith",
  "category": "String information",
  "description": "Returns a boolean array which is True where the string element in a ends with suffix, otherwise False",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.endswith.html",
  "doc": "Returns a boolean array which is \`True\` where the string element in \`a\` ends with \`suffix\`, otherwise \`False\`.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsuffix : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    With optional \`start\`, test beginning at that position. With optional \`end\`, stop comparing at that position.\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def endswith(a, suffix, start=0, end=None):\n    \"\"\"\n    Returns a boolean array which is \`True\` where the string element\n    in \`\`a\`\` ends with \`\`suffix\`\`, otherwise \`\`False\`\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    suffix : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    start, end : array_like, with any integer dtype, optional\n        With optional \`\`start\`\`, test beginning at that position. With\n        optional \`\`end\`\`, stop comparing at that position.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.endswith\n\n    Examples\n    --------\n    >>> s = np.array(['foo', 'bar'])\n    >>> np.strings.endswith(s, 'ar')\n    array([False,  True])\n    >>> np.strings.endswith(s, 'a', start=1, end=2)\n    array([False,  True])\n\n    \"\"\"\n    end = end if end is not None else np.iinfo(np.int64).max\n    return _endswith_ufunc(a, suffix, start, end)"
}
-/

/-- Check if strings in array end with given suffixes -/
def endswith {n : Nat} (a : Vector String n) (suffix : Vector String n) : Id (Vector Bool n) :=
  return Vector.ofFn (fun i => (a.get i).endsWith (suffix.get i))

-- LLM HELPER
theorem string_endswith_properties (s : String) (suffix : String) :
    (s.endsWith suffix = true → 
      suffix.length ≤ s.length ∧
      s.drop (s.length - suffix.length) = suffix) ∧
    (s.endsWith suffix = false → 
      suffix.length > s.length ∨
      s.drop (s.length - suffix.length) ≠ suffix) := by
  constructor
  · intro h
    constructor
    · by_cases h_len : suffix.length ≤ s.length
      · exact h_len
      · have : s.endsWith suffix = false := by
          rw [String.endsWith_iff_suffix] at h
          rw [String.endsWith_iff_suffix, String.isSuffix_iff] at h
          obtain ⟨t, ht⟩ := h
          rw [← ht, String.length_append] at h_len
          simp at h_len
        rw [this] at h
        simp at h
    · rw [String.endsWith_iff_suffix, String.isSuffix_iff] at h
      obtain ⟨t, ht⟩ := h
      rw [← ht]
      simp [String.drop_append]
  · intro h
    by_cases h_len : suffix.length ≤ s.length
    · right
      rw [String.endsWith_iff_suffix, String.isSuffix_iff] at h
      push_neg at h
      intro h_eq
      apply h
      use s.take (s.length - suffix.length)
      rw [String.take_append_drop, h_eq]
    · left
      exact Nat.not_le.mp h_len

/-- Specification: endswith returns boolean array indicating which strings end with corresponding suffixes -/
theorem endswith_spec {n : Nat} (a : Vector String n) (suffix : Vector String n) :
    ⦃⌜True⌝⦄
    endswith a suffix
    ⦃⇓r => ⌜∀ i : Fin n, 
      -- Main specification: result matches String.endsWith for each pair
      (r.get i = (a.get i).endsWith (suffix.get i)) ∧
      -- Mathematical property: if result is true, suffix appears at the end
      (r.get i = true → 
        (suffix.get i).length ≤ (a.get i).length ∧
        (a.get i).drop ((a.get i).length - (suffix.get i).length) = (suffix.get i)) ∧
      -- Mathematical property: if result is false, suffix does not appear at the end
      (r.get i = false → 
        (suffix.get i).length > (a.get i).length ∨
        (a.get i).drop ((a.get i).length - (suffix.get i).length) ≠ (suffix.get i))⌝⦄ := by
  dsimp [endswith]
  intro i
  apply wp_pure_intro
  intro r
  intro i_fin
  constructor
  · simp [Vector.get_ofFn]
  · have h := string_endswith_properties (a.get i_fin) (suffix.get i_fin)
    simp [Vector.get_ofFn]
    exact h