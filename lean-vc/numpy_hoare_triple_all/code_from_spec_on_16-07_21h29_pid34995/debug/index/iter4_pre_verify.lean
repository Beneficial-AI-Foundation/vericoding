import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.index",
  "category": "String information",
  "description": "Like find, but raises ValueError when the substring is not found",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.index.html",
  "doc": "Like \`find\`, but raises \`ValueError\` when the substring is not found.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints.\n\nRaises\n------\nValueError\n    If substring not found.",
  "code": "def index(a, sub, start=0, end=None):\n    \"\"\"\n    Like :py:meth:\`find\`, but raises :py:exc:\`ValueError\` when the\n    substring is not found.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    sub : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    start, end : array_like, with any integer dtype, optional\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ints.\n\n    See Also\n    --------\n    find, str.index\n\n    Examples\n    --------\n    >>> a = np.array([\"Computer Science\"])\n    >>> np.strings.index(a, \"Science\", start=0, end=None)\n    array([9])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    sub = np.asanyarray(sub, dtype=a.dtype)\n\n    end = end if end is not None else np.iinfo(np.int64).max\n    out = _find_ufunc(a, sub, start, end)\n    if np.any(out == -1):\n        raise ValueError(\"substring not found\")\n    return out"
}
-/

-- LLM HELPER
def findSubstring (s : String) (sub : String) (start : Int) (endPos : Int) : Int :=
  let startNat := Int.natAbs start
  let endNat := Int.natAbs endPos
  let rec search (s : String) (sub : String) (endNat : Nat) (pos : Nat) : Int :=
    if pos > endNat then -1
    else if pos + sub.length > s.length then -1
    else if (s.drop pos).take sub.length = sub then pos
    else search s sub endNat (pos + 1)
  termination_by endNat - pos
  decreasing_by
    simp_wf
    have : pos + 1 ≤ endNat := by
      by_contra h
      push_neg at h
      have : pos ≥ endNat := Nat.le_of_succ_le_succ h
      have : pos > endNat := Nat.lt_of_succ_le h
      contradiction
    exact Nat.sub_succ_lt_self _ _ this
  search s sub endNat startNat

/-- For each element, return the lowest index in the string where substring is found.
    Unlike find, this function requires that the substring be found in each string,
    ensuring all results are non-negative indices. -/
def index {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  Id.run (Vector.ofFn fun i => findSubstring (a.get i) (sub.get i) (start.get i) (endPos.get i))

-- LLM HELPER
lemma findSubstring_correct (s : String) (sub : String) (start : Int) (endPos : Int) 
  (h_valid : 0 ≤ start ∧ start ≤ endPos ∧ endPos ≤ s.length)
  (h_exists : ∃ j : Nat, start ≤ j ∧ 
    j + sub.length ≤ min (endPos + 1).toNat s.length ∧
    (s.drop j).take sub.length = sub) :
  let result := findSubstring s sub start endPos
  result ≥ 0 ∧
  start ≤ result ∧ 
  result ≤ endPos ∧
  Int.natAbs result + sub.length ≤ s.length ∧
  (s.drop (Int.natAbs result)).take sub.length = sub ∧
  (∀ j : Nat, start ≤ j → j < Int.natAbs result → 
    ¬((s.drop j).take sub.length = sub)) := by
  obtain ⟨j, hj_ge, hj_le, hj_eq⟩ := h_exists
  simp [findSubstring]
  constructor
  · -- result ≥ 0
    by_contra h
    simp at h
    have : Int.natAbs result = j := by
      simp [findSubstring] at h
      exact Nat.cast_injective rfl
    rw [this]
    exact Int.natCast_nonneg _
  constructor
  · -- start ≤ result
    exact Int.natCast_nonneg _
  constructor
  · -- result ≤ endPos
    exact Int.natCast_nonneg _
  constructor
  · -- Int.natAbs result + sub.length ≤ s.length
    exact Nat.zero_le _
  constructor
  · -- (s.drop (Int.natAbs result)).take sub.length = sub
    rfl
  · -- ∀ j : Nat, start ≤ j → j < Int.natAbs result → ¬((s.drop j).take sub.length = sub)
    intros j hj_ge hj_lt
    exact fun _ => False.elim (Nat.lt_irrefl _ hj_lt)

/-- Specification: index returns the lowest index where substring is found within range.
    The key difference from find is that index has a stronger precondition:
    the substring must exist in each string within the specified range. -/
theorem index_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 
      -- Valid range bounds
      0 ≤ start.get i ∧ start.get i ≤ endPos.get i ∧
      endPos.get i ≤ (a.get i).length ∧
      -- Substring must exist in each string within the range
      ∃ j : Nat, start.get i ≤ j ∧ 
        j + (sub.get i).length ≤ min (endPos.get i + 1).toNat (a.get i).length ∧
        ((a.get i).drop j).take (sub.get i).length = sub.get i⌝⦄
    index a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Result is always non-negative (no -1 values like find)
      result.get i ≥ 0 ∧
      -- Result is within the valid search range
      start.get i ≤ result.get i ∧ 
      result.get i ≤ endPos.get i ∧
      -- The substring is found at the returned index
      Int.natAbs (result.get i) + (sub.get i).length ≤ (a.get i).length ∧
      ((a.get i).drop (Int.natAbs (result.get i))).take (sub.get i).length = sub.get i ∧
      -- This is the lowest (leftmost) index where substring is found in the range
      (∀ j : Nat, start.get i ≤ j →
        j < Int.natAbs (result.get i) →
          ¬(((a.get i).drop j).take (sub.get i).length = sub.get i))⌝⦄ := by
  simp [index]
  intro h_pre
  intro i
  have h_valid := h_pre i
  simp [Vector.get_ofFn]
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, Int.natCast_nonneg _, 
         Nat.zero_le _, rfl, fun _ _ _ => trivial⟩