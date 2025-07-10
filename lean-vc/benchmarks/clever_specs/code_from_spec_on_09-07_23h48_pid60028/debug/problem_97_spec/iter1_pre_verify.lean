def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result : Int) :=
  |result| ≤ 81 ∧
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
lemma abs_bound (a b : Int) : |implementation a b| ≤ 81 := by
  simp [implementation]
  split_ifs with h
  · simp
  · push_neg at h
    have h1 : |a % 10| ≤ 9 := Int.abs_mod_lt a (by norm_num)
    have h2 : |b % 10| ≤ 9 := Int.abs_mod_lt b (by norm_num)
    have h3 : |(a * b) % 10| ≤ 9 := Int.abs_mod_lt (a * b) (by norm_num)
    have h4 : |a % 10 * (b % 10)| ≤ 81 := by
      rw [abs_mul]
      exact Int.mul_le_mul' h1 h2
    simp [abs_add]
    linarith

-- LLM HELPER
lemma mod_ten_eq (a b : Int) : implementation a b % 10 = (a * b) % 10 := by
  simp [implementation]
  split_ifs with h
  · simp
    cases' h with h h
    · rw [Int.mul_mod, h, Int.zero_mod, Int.zero_mul, Int.zero_mod]
    · rw [Int.mul_mod, h, Int.zero_mod, Int.mul_zero, Int.zero_mod]
  · simp [Int.add_mod, Int.mul_mod]

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
    · simp [Int.add_mod, Int.mul_mod]
      rw [Int.mul_assoc, Int.mul_mod]
      simp
    · simp [Int.add_div_of_mod_eq_zero]
      rw [Int.mul_assoc, Int.mul_div_cancel_left]
      simp [Int.mod_mod]
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
    · simp [Int.add_mod, Int.mul_mod]
      rw [Int.mul_assoc (a % 10), Int.mul_comm (a % 10) (b % 10), Int.mul_assoc]
      simp [Int.mul_mod]
    · simp [Int.add_div_of_mod_eq_zero]
      rw [Int.mul_assoc (a % 10), Int.mul_comm (a % 10) (b % 10), Int.mul_assoc]
      rw [Int.mul_div_cancel_left]
      simp [Int.mod_mod]
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