def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l[i]! ≤ result) ∧
  (∃ i, i < l.length ∧ l[i]! = result));
-- program termination
∃ result, implementation l = result ∧
spec result

-- LLM HELPER
def list_max (l: List Int) : Int :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => max x (list_max xs)

def implementation (l: List Int) : Int := list_max l

-- LLM HELPER
lemma list_max_ge_elements (l: List Int) (i: Nat) (h: i < l.length) : l[i]! ≤ list_max l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => 
      simp [List.getElem_cons_zero, list_max]
      exact le_max_left x (list_max xs)
    | succ j =>
      simp [List.getElem_cons_succ, list_max]
      have h' : j < xs.length := by simp at h; exact h
      have : xs[j]! ≤ list_max xs := ih j h'
      exact le_trans this (le_max_right x (list_max xs))

-- LLM HELPER
lemma list_max_exists_in_list (l: List Int) (h: l.length > 0) : ∃ i, i < l.length ∧ l[i]! = list_max l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp [list_max]
    by_cases h_xs : xs = []
    · simp [h_xs, List.getElem_cons_zero]
      use 0
      simp
    · have h_xs_len : xs.length > 0 := by
        cases xs with
        | nil => contradiction
        | cons y ys => simp
      have ih_result := ih h_xs_len
      obtain ⟨j, hj_lt, hj_eq⟩ := ih_result
      by_cases h_max : x ≥ list_max xs
      · have : max x (list_max xs) = x := max_eq_left h_max
        use 0
        simp [List.getElem_cons_zero, this]
      · have : max x (list_max xs) = list_max xs := max_eq_right (le_of_not_ge h_max)
        use j + 1
        simp [List.getElem_cons_succ, this, hj_eq]
        exact Nat.succ_lt_succ hj_lt

theorem correctness
(l: List Int)
: problem_spec implementation l := by
  unfold problem_spec implementation
  use list_max l
  constructor
  · rfl
  · intro h
    constructor
    · exact list_max_ge_elements l
    · exact list_max_exists_in_list l h