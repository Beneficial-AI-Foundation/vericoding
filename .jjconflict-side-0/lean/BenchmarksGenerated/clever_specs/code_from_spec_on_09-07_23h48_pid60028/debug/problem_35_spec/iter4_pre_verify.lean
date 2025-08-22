def problem_spec
(implementation: List Int → Int)
(l: List Int) :=
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l[i]?.getD 0 ≤ result) ∧
  (∃ i, i < l.length ∧ l[i]?.getD 0 = result));
∃ result, implementation l = result ∧ spec result

-- LLM HELPER
def list_max (l: List Int) : Int :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => max x (list_max xs)

def implementation (l: List Int) : Int := list_max l

-- LLM HELPER
lemma list_max_upper_bound (l: List Int) (h: l.length > 0) :
  ∀ i, i < l.length → l[i]?.getD 0 ≤ list_max l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    intro i hi
    simp [list_max]
    by_cases h_eq : i = 0
    · simp [h_eq, List.getElem?_cons_zero]
      exact le_max_left x (list_max xs)
    · have hi_pos : i > 0 := Nat.pos_of_ne_zero h_eq
      have hi_pred : i - 1 < xs.length := by
        simp [List.length] at hi
        omega
      simp [List.getElem?_cons_succ]
      cases' xs with y ys
      · simp [List.length] at hi_pred
      · apply le_trans (ih (by simp [List.length]; omega) (i - 1) hi_pred)
        exact le_max_right x (list_max (y :: ys))

-- LLM HELPER
lemma list_max_achievable (l: List Int) (h: l.length > 0) :
  ∃ i, i < l.length ∧ l[i]?.getD 0 = list_max l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp [list_max]
    by_cases h_empty : xs = []
    · simp [h_empty, List.getElem?_cons_zero]
      exact ⟨0, by simp [List.length], rfl⟩
    · have xs_nonempty : xs.length > 0 := by
        cases xs
        · contradiction
        · simp [List.length]
      by_cases h_max : x ≥ list_max xs
      · simp [max_def, h_max, List.getElem?_cons_zero]
        exact ⟨0, by simp [List.length], rfl⟩
      · simp [max_def, h_max]
        have h_max' : list_max xs > x := lt_of_not_ge h_max
        obtain ⟨i, hi_bound, hi_eq⟩ := ih xs_nonempty
        exact ⟨i + 1, by simp [List.length]; omega, by simp [List.getElem?_cons_succ]; exact hi_eq⟩

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  simp [problem_spec, implementation]
  use list_max l
  constructor
  · rfl
  · intro h
    constructor
    · exact list_max_upper_bound l h
    · exact list_max_achievable l h