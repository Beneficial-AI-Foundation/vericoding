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
  pure (a.map String.length)

-- LLM HELPER
lemma string_length_nonneg (s : String) : s.length ≥ 0 := by
  exact Nat.zero_le s.length

-- LLM HELPER
lemma string_empty_iff_length_zero (s : String) : s = "" ↔ s.length = 0 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact String.eq_empty_of_length_eq_zero h

-- LLM HELPER
lemma string_single_char_length_one (s : String) : s ≠ "" ∧ s.drop 1 = "" → s.length = 1 := by
  intro ⟨h1, h2⟩
  have h3 : s.length > 0 := by
    by_contra h
    push_neg at h
    have : s.length = 0 := Nat.eq_zero_of_le_zero h
    rw [string_empty_iff_length_zero] at this
    exact h1 this
  have h4 : s.length ≤ 1 := by
    by_contra h
    push_neg at h
    have : s.length ≥ 2 := h
    have : s.drop 1 ≠ "" := by
      apply String.ne_empty_of_length_pos
      rw [String.length_drop]
      omega
    exact this h2
  omega

-- LLM HELPER
lemma string_take_length_le (s : String) (k : Nat) : (s.take k).length ≤ s.length := by
  rw [String.length_take]
  exact Nat.min_le_right k s.length

-- LLM HELPER
lemma string_length_deterministic (s1 s2 : String) : s1 = s2 → s1.length = s2.length := by
  intro h
  rw [h]

-- LLM HELPER
lemma string_length_append (s1 s2 : String) : (s1 ++ s2).length = s1.length + s2.length := by
  exact String.length_append s1 s2

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
  apply Triple.pure_spec
  intro i
  constructor
  · -- Basic correctness
    simp [str_len]
    rfl
  constructor
  · -- Non-negativity
    simp [str_len]
    apply string_length_nonneg
  constructor
  · -- Empty string property
    simp [str_len]
    apply string_empty_iff_length_zero
  constructor
  · -- Single character property
    simp [str_len]
    apply string_single_char_length_one
  constructor
  · -- Monotonicity property
    simp [str_len]
    intro k hk
    apply string_take_length_le
  constructor
  · -- Deterministic property
    simp [str_len]
    intro j h
    apply string_length_deterministic
    exact h
  · -- Concatenation property
    simp [str_len]
    intro s1 s2 h
    rw [h]
    apply string_length_append