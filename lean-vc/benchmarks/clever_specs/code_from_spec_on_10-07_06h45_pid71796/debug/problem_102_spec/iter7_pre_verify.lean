def problem_spec
(implementation: Int → Int → Int)
(x: Int) (y: Int) :=
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (∀ i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y)))
∃ result, implementation x y = result ∧
spec result

-- LLM HELPER
def Even (n: Int) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def Odd (n: Int) : Prop := ∃ k, n = 2 * k + 1

def implementation (x: Int) (y: Int) : Int :=
  if x > y then -1
  else if (x == y) = true ∧ x % 2 = 1 then -1
  else if y % 2 = 0 then y
  else y - 1

-- LLM HELPER
lemma even_iff_mod_two_eq_zero (n: Int) : Even n ↔ n % 2 = 0 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    simp [Int.mul_emod]
  · intro h
    use n / 2
    rw [Int.mul_comm]
    exact Int.mul_eDiv_cancel_of_emod_eq_zero h

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n: Int) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk]
    simp [Int.add_mul_emod_self_left]
  · intro h
    use (n - 1) / 2
    rw [Int.mul_comm]
    have : n = 2 * ((n - 1) / 2) + 1 := by
      rw [← Int.add_mul_eDiv_right (n - 1) (by norm_num : (2 : Int) ≠ 0)]
      simp [Int.sub_emod, h]
      ring
    exact this.symm

-- LLM HELPER
lemma odd_not_even (n: Int) : Odd n → ¬Even n := by
  intro ⟨k, hk⟩ ⟨j, hj⟩
  have : 2 * k + 1 = 2 * j := by rw [← hk, hj]
  have : 1 = 2 * (j - k) := by linarith
  have : 1 % 2 = 0 := by
    rw [this]
    simp [Int.mul_emod]
  norm_num at this

-- LLM HELPER
lemma int_eq_iff_beq (x y: Int) : x = y ↔ (x == y) = true := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact Int.eq_iff_beq.mpr h

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y := by
  unfold problem_spec implementation
  use if x > y then -1 else if (x == y) = true ∧ x % 2 = 1 then -1 else if y % 2 = 0 then y else y - 1
  simp
  split_ifs with h1 h2 h3
  · -- Case: x > y
    constructor
    · left; rfl
    constructor
    · left; rfl
    · constructor
      · intro h
        left
        exact h1
      · intro h
        cases' h with h' h'
        · exact h'
        · exfalso
          have : x ≤ y := le_of_not_gt h'
          exact not_le.mpr h1 this
  · -- Case: x ≤ y ∧ x = y ∧ x % 2 = 1
    constructor
    · left; rfl
    constructor
    · left; rfl
    · constructor
      · intro h
        right
        constructor
        · rw [int_eq_iff_beq]
          exact h2.1
        · constructor
          · rw [odd_iff_mod_two_eq_one]
            exact h2.2
          · rw [odd_iff_mod_two_eq_one]
            rw [← int_eq_iff_beq.mpr h2.1]
            exact h2.2
      · intro h
        cases' h with h' h'
        · exact h'
        · rw [int_eq_iff_beq] at h'
          exact ⟨h'.1, by rw [odd_iff_mod_two_eq_one] at h'.2.1; exact h'.2.1⟩
  · -- Case: x ≤ y ∧ ¬(x = y ∧ x % 2 = 1) ∧ y % 2 = 0
    constructor
    · right
      constructor
      · exact le_of_not_gt h1
      constructor
      · rfl
      · rw [even_iff_mod_two_eq_zero]
        exact h3
    constructor
    · right
      intro i hi
      exact hi.2.1
    · constructor
      · intro h
        exfalso
        have : Even y := by
          rw [even_iff_mod_two_eq_zero]
          exact h3
        cases' h with h' h'
        · exact not_le.mpr h' (le_of_not_gt h1)
        · rw [int_eq_iff_beq] at h'
          have : Odd y := h'.2.2
          exact odd_not_even y this this
      · intro h
        cases' h with h' h'
        · exact le_of_not_gt h1
        · exfalso
          rw [int_eq_iff_beq] at h'
          have : y % 2 = 1 := by
            rw [odd_iff_mod_two_eq_one] at h'.2.2
            exact h'.2.2
          rw [this] at h3
          norm_num at h3
  · -- Case: x ≤ y ∧ ¬(x = y ∧ x % 2 = 1) ∧ y % 2 = 1
    constructor
    · right
      constructor
      · exact le_of_not_gt h1
      constructor
      · simp [Int.sub_le_iff_le_add]
      · rw [even_iff_mod_two_eq_zero]
        rw [Int.sub_emod]
        simp [h3]
    constructor
    · right
      intro i hi
      have : i ≤ y := hi.2.1
      have : i ≠ y := by
        intro heq
        rw [heq] at hi
        have : Even y := hi.2.2
        have : Odd y := by
          rw [odd_iff_mod_two_eq_one]
          exact h3
        exact odd_not_even y this this
      exact Int.le_sub_one_of_lt (lt_of_le_of_ne this this)
    · constructor
      · intro h
        exfalso
        push_neg at h1
        simp at h2
        push_neg at h2
        cases' h with h' h'
        · exact not_le.mpr h' h1
        · rw [int_eq_iff_beq] at h'
          apply h2
          constructor
          · exact h'.1
          · rw [odd_iff_mod_two_eq_one] at h'.2.1
            exact h'.2.1
      · intro h
        cases' h with h' h'
        · exact le_of_not_gt h1
        · exfalso
          rw [int_eq_iff_beq] at h'
          have : y % 2 = 1 := by
            rw [odd_iff_mod_two_eq_one] at h'.2.2
            exact h'.2.2
          rw [this] at h3
          norm_num at h3