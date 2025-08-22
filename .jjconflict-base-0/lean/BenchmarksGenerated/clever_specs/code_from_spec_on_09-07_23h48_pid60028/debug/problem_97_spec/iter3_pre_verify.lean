def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) : Prop :=
-- spec
let spec (result : Int) :=
  Int.natAbs result ≤ 81 ∧
  result % 10 = (a * b) % 10 ∧
  ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10))) ∧
  ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10))) ∧
  ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
-- program termination
∃ result,
  implementation a b = result ∧
  spec result

def implementation (a b: Int) : Int := 
  if a % 10 = 0 ∨ b % 10 = 0 then 0
  else (a % 10) * (b % 10) * 10 + (a * b) % 10

-- LLM HELPER
lemma abs_bound (a b : Int) : Int.natAbs (implementation a b) ≤ 81 := by
  simp [implementation]
  split_ifs with h
  · simp
  · push_neg at h
    have h1 : Int.natAbs (a % 10) ≤ 9 := by
      have : Int.natAbs (a % 10) < 10 := Int.natAbs_mod_lt a (by norm_num : (0 : Int) < 10)
      omega
    have h2 : Int.natAbs (b % 10) ≤ 9 := by
      have : Int.natAbs (b % 10) < 10 := Int.natAbs_mod_lt b (by norm_num : (0 : Int) < 10)
      omega
    have h3 : Int.natAbs ((a * b) % 10) ≤ 9 := by
      have : Int.natAbs ((a * b) % 10) < 10 := Int.natAbs_mod_lt (a * b) (by norm_num : (0 : Int) < 10)
      omega
    have h4 : Int.natAbs (a % 10 * (b % 10) * 10) ≤ 90 := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
      have : Int.natAbs (a % 10 * (b % 10)) ≤ 81 := by
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul' h1 h2
      simp
      omega
    have h5 : Int.natAbs (a % 10 * (b % 10) * 10 + (a * b) % 10) ≤ 90 + 9 := by
      exact Int.natAbs_add_le _ _
    omega

-- LLM HELPER
lemma mod_ten_eq (a b : Int) : implementation a b % 10 = (a * b) % 10 := by
  simp [implementation]
  split_ifs with h
  · simp
    cases' h with h h
    · rw [Int.mul_emod, h, Int.zero_mod, Int.zero_mul, Int.zero_mod]
    · rw [Int.mul_emod, h, Int.zero_mod, Int.mul_zero, Int.zero_mod]
  · simp [Int.add_emod, Int.mul_emod]

-- LLM HELPER
lemma divisibility_b (a b : Int) : (b % 10) ≠ 0 → (implementation a b % (b % 10) = 0 ∧ (implementation a b / (b % 10)) % 100 = (a % 10)) := by
  intro h
  simp [implementation]
  split_ifs with h_cases
  · cases' h_cases with h1 h2
    · simp at h1
      contradiction
    · simp at h2
      contradiction
  · constructor
    · simp [Int.add_emod, Int.mul_emod]
      rw [Int.mul_assoc, Int.mul_emod]
      simp
    · have : (a % 10 * (b % 10) * 10 + (a * b) % 10) % (b % 10) = 0 := by
        simp [Int.add_emod, Int.mul_emod]
        rw [Int.mul_assoc, Int.mul_emod]
        simp
      rw [Int.add_ediv_of_emod_eq_zero this]
      rw [Int.mul_assoc, Int.mul_ediv_cancel_left]
      simp [Int.emod_emod_of_dvd]
      exact h

-- LLM HELPER
lemma divisibility_a (a b : Int) : (a % 10) ≠ 0 → (implementation a b % (a % 10) = 0 ∧ (implementation a b / (a % 10)) % 100 = (b % 10)) := by
  intro h
  simp [implementation]
  split_ifs with h_cases
  · cases' h_cases with h1 h2
    · simp at h1
      contradiction
    · simp at h2
      contradiction
  · constructor
    · simp [Int.add_emod, Int.mul_emod]
      rw [Int.mul_assoc (a % 10), Int.mul_comm (a % 10) (b % 10), Int.mul_assoc]
      simp [Int.mul_emod]
    · have : (a % 10 * (b % 10) * 10 + (a * b) % 10) % (a % 10) = 0 := by
        simp [Int.add_emod, Int.mul_emod]
        rw [Int.mul_assoc (a % 10), Int.mul_comm (a % 10) (b % 10), Int.mul_assoc]
        simp [Int.mul_emod]
      rw [Int.add_ediv_of_emod_eq_zero this]
      rw [Int.mul_assoc (a % 10), Int.mul_comm (a % 10) (b % 10), Int.mul_assoc]
      rw [Int.mul_ediv_cancel_left]
      simp [Int.emod_emod_of_dvd]
      exact h

-- LLM HELPER
lemma zero_case (a b : Int) : ((a % 10 = 0) ∨ (b % 10 = 0)) → implementation a b = 0 := by
  intro h
  simp [implementation]
  split_ifs with h_cases
  · rfl
  · push_neg at h_cases
    cases' h with h1 h2
    · contradiction
    · contradiction

theorem correctness
(a b: Int)
: problem_spec implementation a b := by
  simp [problem_spec]
  use implementation a b
  constructor
  · rfl
  · constructor
    · exact abs_bound a b
    · constructor
      · exact mod_ten_eq a b
      · constructor
        · exact divisibility_b a b
        · constructor
          · exact divisibility_a a b
          · exact zero_case a b