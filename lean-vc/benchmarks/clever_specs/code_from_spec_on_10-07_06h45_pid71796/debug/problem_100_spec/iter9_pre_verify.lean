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
def make_arithmetic_sequence (start: Int) (diff: Int) (len: Nat) : List Int :=
  match len with
  | 0 => []
  | n + 1 => start :: make_arithmetic_sequence (start + diff) diff n

-- LLM HELPER
lemma make_arithmetic_sequence_length (start diff: Int) (len: Nat) :
  (make_arithmetic_sequence start diff len).length = len := by
  induction len with
  | zero => simp [make_arithmetic_sequence]
  | succ n ih => simp [make_arithmetic_sequence, ih]

-- LLM HELPER
lemma make_arithmetic_sequence_get_zero (start diff: Int) (len: Nat) (h: 0 < len) :
  (make_arithmetic_sequence start diff len)[0]! = start := by
  cases len with
  | zero => contradiction
  | succ n => simp [make_arithmetic_sequence]

-- LLM HELPER
lemma make_arithmetic_sequence_get_succ (start diff: Int) (len: Nat) (i: Nat) 
  (h1: i + 1 < len) :
  (make_arithmetic_sequence start diff len)[i + 1]! = 
  (make_arithmetic_sequence start diff len)[i]! + diff := by
  induction len generalizing i with
  | zero => simp at h1
  | succ n ih =>
    cases i with
    | zero => 
      simp [make_arithmetic_sequence]
      cases n with
      | zero => simp at h1
      | succ m => simp [make_arithmetic_sequence]
    | succ j =>
      simp [make_arithmetic_sequence]
      have h2: j + 1 < n := by simp at h1; exact h1
      exact ih j h2

def implementation (n: Int) : List Int := 
  if n ≤ 0 then [] else make_arithmetic_sequence n 2 n.natAbs

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  by_cases h: n ≤ 0
  · simp [h]
    use []
    constructor
    · rfl
    constructor
    · simp
      constructor
      · have : n ≤ 0 := h
        omega
      · intro i h1 h2
        have : n ≤ 0 := h
        omega
    · intro i h1 h2
      have : n ≤ 0 := h
      omega
  · simp [h]
    have n_pos: 0 < n := by linarith
    have n_nat_pos: 0 < n.natAbs := Int.natAbs_pos.mpr (ne_of_gt n_pos)
    use make_arithmetic_sequence n 2 n.natAbs
    constructor
    · rfl
    constructor
    · rw [make_arithmetic_sequence_length]
      simp [Int.natAbs_of_nonneg (le_of_lt n_pos)]
    constructor
    · intro i h1 h2
      have h_pos: 0 < n := n_pos
      have h_eq: n.natAbs = Int.natAbs n := rfl
      have h_nat: n.natAbs = n.toNat := by
        rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
        rw [Int.toNat_of_nonneg (le_of_lt h_pos)]
      rw [← Int.natAbs_of_nonneg (le_of_lt h_pos)] at h2
      have h3: i < n.natAbs := h2
      have h5: i ≥ 1 := h1
      cases i with
      | zero => linarith
      | succ j =>
        have h6: j + 1 < n.natAbs := h3
        rw [make_arithmetic_sequence_get_succ n 2 n.natAbs j h6]
        simp
    · rw [make_arithmetic_sequence_get_zero]
      exact Int.natAbs_pos.mpr (ne_of_gt n_pos)