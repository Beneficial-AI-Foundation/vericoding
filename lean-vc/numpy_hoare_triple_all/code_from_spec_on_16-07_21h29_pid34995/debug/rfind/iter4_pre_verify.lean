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

-- LLM HELPER
def rfind_single (s : String) (sub : String) (start : Int) (endPos : Int) : Int :=
  let len := s.length
  let sub_len := sub.length
  let start_nat := Int.natAbs start
  let end_nat := Int.natAbs endPos
  let effective_end := min end_nat (len - 1)
  
  if sub_len = 0 then effective_end
  else if start < 0 ∨ start_nat >= len ∨ start > endPos ∨ sub_len > len then -1
  else
    let search_end := if effective_end + 1 < sub_len then 0 else effective_end + 1 - sub_len
    let rec search_from (pos : Nat) : Int :=
      if pos < start_nat then -1
      else if pos + sub_len <= len ∧ String.startsWith (s.drop pos) sub then Int.ofNat pos
      else if pos = 0 then -1
      else search_from (pos - 1)
    search_from search_end

/-- For each element, return the highest index in the string where substring is found -/
def rfind {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  pure ⟨Array.mk (Vector.ofFn (fun i => rfind_single (a.get i) (sub.get i) (start.get i) (endPos.get i))).toArray, by simp [Vector.ofFn_size]⟩

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
  simp [rfind]
  simp [Triple.bind_wp, Triple.pure_wp]
  intro h i
  constructor
  · -- Basic range constraint
    simp [rfind_single]
    split_ifs with h1 h2 h3
    · right
      simp [Int.ofNat_nonneg]
      have : min (Int.natAbs (endPos.get i)) ((a.get i).length - 1) < (a.get i).length := by
        simp [min_lt_iff]
        exact Nat.sub_lt (Nat.pos_of_ne_zero (ne_of_gt (Nat.zero_lt_succ _))) (Nat.le_refl _)
      exact Int.ofNat_lt_ofNat.mpr this
    · left; rfl
    · left; rfl
    · left; rfl
  constructor
  · -- If result is -1, no occurrence
    intro h_neg1 j hj
    simp [rfind_single] at h_neg1
    split_ifs at h_neg1 with h1 h2 h3
    · contradiction
    · simp at h_neg1
    · have : 0 ≤ start.get i := (h i).1
      cases' h3 with h3a h3b
      cases' h3b with h3b h3c
      cases' h3c with h3c h3d
      · linarith
      · have : Int.natAbs (start.get i) ≥ (a.get i).length := h3b
        have : start.get i ≤ ↑j := hj.1
        have : 0 ≤ start.get i := (h i).1
        simp [Int.natAbs_eq] at this
        linarith [hj.2.2]
      · have : start.get i ≤ endPos.get i := (h i).2
        linarith
      · have : (sub.get i).length > (a.get i).length := h3d
        linarith [hj.2.2]
    · simp
  · -- If result is non-negative, it's the rightmost valid occurrence
    intro h_pos
    simp [rfind_single] at h_pos
    split_ifs at h_pos with h1 h2 h3
    · -- Empty substring case
      simp at h_pos ⊢
      constructor
      · exact (h i).1
      constructor
      · simp [Int.natAbs_eq] at h_pos
        have : 0 ≤ endPos.get i := le_trans (h i).1 (h i).2
        simp [Int.natAbs_eq] at h_pos
        linarith
      constructor
      · simp [String.startsWith_drop_zero]
        rfl
      · intro j hj
        simp
    · contradiction
    · contradiction
    · simp only [Int.ofNat_nonneg, not_false_eq_true, true_and] at h_pos
      simp