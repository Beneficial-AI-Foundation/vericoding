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
lemma nat_cast_length (l : List Int) : (l.length : Int) = l.length := by simp

-- LLM HELPER
lemma generate_sequence_length (n : Int) (acc : List Int) : 
  n > 0 → acc.length < n.natAbs → (generate_sequence n acc).length = n.natAbs := by
  intros h_pos h_lt
  induction' n.natAbs using Nat.strong_induction with k ih generalizing acc
  simp only [generate_sequence]
  split_ifs with h
  · simp at h
    omega
  · simp at h
    have : acc.length + 1 < k := by
      rw [Int.natAbs_of_nonneg (le_of_lt h_pos)] at h_lt
      omega
    have next_acc : (acc ++ [if acc.isEmpty then n else acc.getLast! + 2]).length = acc.length + 1 := by simp
    rw [← next_acc]
    apply ih (acc.length + 1)
    · exact this
    · exact h_pos
    · rw [next_acc]
      exact this

-- LLM HELPER
lemma generate_sequence_first (n : Int) : 
  n > 0 → (generate_sequence n [])[0]! = n := by
  intro h_pos
  simp only [generate_sequence]
  split_ifs with h
  · simp at h
    rw [Int.natAbs_of_nonneg (le_of_lt h_pos)] at h
    omega
  · simp [List.get!]

-- LLM HELPER
lemma generate_sequence_step (n : Int) (acc : List Int) (i : Nat) :
  n > 0 → acc.length < n.natAbs → 1 ≤ i → i < n.natAbs → 
  (generate_sequence n acc)[i]! = (generate_sequence n acc)[i-1]! + 2 := by
  intros h_pos h_lt h_ge h_lt_n
  induction' n.natAbs using Nat.strong_induction with k ih generalizing acc
  simp only [generate_sequence]
  split_ifs with h
  · simp at h
    omega
  · simp at h
    have next_acc : (acc ++ [if acc.isEmpty then n else acc.getLast! + 2]).length = acc.length + 1 := by simp
    rw [← next_acc]
    apply ih (acc.length + 1)
    · rw [next_acc]
      omega
    · exact h_pos
    · rw [next_acc]
      omega
    · exact h_ge
    · exact h_lt_n

theorem correctness
(n: Int) :
problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · simp
      constructor
      · simp
      constructor
      · intro i hi
        simp at hi
        exact False.elim (Nat.not_lt_zero i hi.2)
      · intro h_pos
        simp at h_pos
        exact absurd h_pos h
    · have n_pos : n > 0 := by
        by_contra h_neg
        simp at h_neg
        exact h h_neg
      constructor
      · simp [generate_sequence]
        rw [nat_cast_length]
        rw [Int.natAbs_of_nonneg (le_of_lt n_pos)]
        exact generate_sequence_length n [] n_pos (by simp)
      constructor
      · intro i hi
        simp at hi
        rw [Int.natAbs_of_nonneg (le_of_lt n_pos)] at hi
        exact generate_sequence_step n [] i n_pos (by simp) hi.1 hi.2
      · exact generate_sequence_first n n_pos