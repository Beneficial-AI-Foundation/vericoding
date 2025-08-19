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
        split_ifs with h_cond
        · simp at h_cond
          have : n.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt n_pos)
          omega
        · simp
          rw [nat_cast_length]
          rw [Int.natAbs_of_nonneg (le_of_lt n_pos)]
          exact n_pos
      constructor
      · intro i hi
        simp at hi
        simp [generate_sequence]
        split_ifs with h_cond
        · simp at h_cond
          have : n.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt n_pos)
          have : i < n.natAbs := by
            rw [← Int.natAbs_of_nonneg (le_of_lt n_pos)]
            exact hi.2
          omega
        · simp
          sorry
      · simp [generate_sequence]
        split_ifs with h_cond
        · simp at h_cond
          have : n.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt n_pos)
          omega
        · simp
          rfl