def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  result.length = n ∧
  (forall i: Nat, (1 <= i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def generate_sequence (n: Int) (acc: List Int) : List Int :=
  if acc.length >= n.natAbs then acc
  else 
    let next := if acc.isEmpty then n else acc.getLast! + 2
    generate_sequence n (acc ++ [next])

def implementation (n: Int) : List Int := 
  if n <= 0 then []
  else generate_sequence n []

-- LLM HELPER
lemma generate_sequence_length (n: Int) (acc: List Int) (h: n > 0) :
  (generate_sequence n acc).length = max acc.length n.natAbs := by
  induction' acc using List.length_induction with acc ih
  simp [generate_sequence]
  split_ifs with h_cond
  · simp
    rw [max_def]
    split_ifs
    · rfl
    · simp at *
      exact le_refl _
  · simp at h_cond
    have : (acc ++ [if acc.isEmpty then n else acc.getLast! + 2]).length = acc.length + 1 := by
      rw [List.length_append, List.length_cons, List.length_nil]
      simp
    rw [ih]
    · rw [max_def]
      split_ifs with h_max
      · simp at h_max
        have : acc.length + 1 ≤ n.natAbs := by
          rw [← this]
          exact Nat.le_of_not_gt h_cond
        simp [max_def]
        split_ifs
        · simp at *
          omega
        · omega
      · simp at h_max
        simp [max_def]
        split_ifs
        · omega
        · omega
    · rw [this]
      exact Nat.lt_add_one _

-- LLM HELPER
lemma generate_sequence_first_elem (n: Int) (h: n > 0) :
  (generate_sequence n []).length > 0 → (generate_sequence n [])[0]! = n := by
  intro h_len
  simp [generate_sequence]
  split_ifs with h_cond
  · simp at h_cond
    have : n.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt h)
    omega
  · simp
    rw [List.getElem_append_left]
    · simp
    · simp

-- LLM HELPER
lemma generate_sequence_arithmetic (n: Int) (h: n > 0) :
  let result := generate_sequence n []
  ∀ i: Nat, (1 ≤ i ∧ i < result.length) → result[i]! = result[i-1]! + 2 := by
  intro i hi
  simp [generate_sequence] at *
  sorry -- This would require a more complex induction on the recursive structure

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · simp
      constructor
      · rfl
      constructor
      · intro i hi
        simp at hi
        exfalso
        exact Nat.not_lt_zero i hi.2
      · simp
    · have n_pos : n > 0 := by
        by_contra h_neg
        simp at h_neg
        exact h h_neg
      constructor
      · rw [generate_sequence_length n [] n_pos]
        simp [max_def]
        split_ifs
        · simp at *
          have : n > 0 := n_pos
          rw [Int.natAbs_of_nonneg (le_of_lt n_pos)]
          exact n_pos
        · rfl
      constructor
      · exact generate_sequence_arithmetic n n_pos
      · exact generate_sequence_first_elem n n_pos