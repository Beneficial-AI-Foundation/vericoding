def problem_spec
(implementation: Int → Int → Bool)
(x: Int) (n: Int) :=
let spec (result: Bool) :=
  result → exists k: Nat, x = n^k
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def is_perfect_power (x: Int) (n: Int) : Bool :=
  if n = 0 then false
  else if n = 1 then x = 1
  else if n = -1 then x = 1 ∨ x = -1
  else if x = 0 then true
  else if x = 1 then true
  else if x = -1 then n % 2 = 0
  else if x < 0 ∧ n % 2 = 0 then false
  else
    let abs_x := Int.natAbs x
    let abs_n := Int.natAbs n
    let rec check_power (abs_n: Nat) (current: Nat) (power: Nat) (target: Nat) : Bool :=
      if current = target then true
      else if current > target then false
      else check_power abs_n (current * abs_n) (power + 1) target
    termination_by (target - current)
    if abs_n ≤ 1 then false
    else check_power abs_n abs_n 1 abs_x

def implementation (x: Int) (n: Int) : Bool := is_perfect_power x n

-- LLM HELPER
lemma pow_pos_of_pos {a : Int} {k : Nat} (ha : a > 0) : a^k > 0 := by
  induction k with
  | zero => simp
  | succ k ih => 
    simp [Int.pow_succ]
    exact Int.mul_pos ha ih

-- LLM HELPER
lemma pow_neg_even {a : Int} {k : Nat} (ha : a < 0) (hk : k % 2 = 0) : a^k > 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases' Nat.mod_two_eq_zero_or_one k with h h
    · simp [Int.pow_succ]
      have : k % 2 = 0 := h
      have pos_k : a^k > 0 := pow_neg_even ha this
      exact Int.mul_neg_neg_of_neg_of_pos ha pos_k
    · simp [Int.pow_succ]
      have : k % 2 = 1 := h
      have : (k + 1) % 2 = 0 := by
        rw [Nat.add_mod, h]
        simp
      rw [this] at hk
      have neg_k : a^k < 0 := by
        apply pow_neg_odd ha h
      exact Int.mul_neg_pos_of_neg_of_neg ha neg_k

-- LLM HELPER
lemma pow_neg_odd {a : Int} {k : Nat} (ha : a < 0) (hk : k % 2 = 1) : a^k < 0 := by
  induction k with
  | zero => 
    simp at hk
  | succ k ih =>
    cases' Nat.mod_two_eq_zero_or_one k with h h
    · simp [Int.pow_succ]
      have : k % 2 = 0 := h
      have pos_k : a^k > 0 := pow_neg_even ha this
      exact Int.mul_neg_pos_of_neg_of_pos ha pos_k
    · simp [Int.pow_succ]
      have : k % 2 = 1 := h
      have neg_k : a^k < 0 := ih h
      exact Int.mul_pos ha neg_k

-- LLM HELPER
lemma perfect_power_characterization (x n : Int) : 
  (∃ k : Nat, x = n^k) ↔ 
  (n = 0 ∧ x = 0) ∨ 
  (n = 1 ∧ x = 1) ∨ 
  (n = -1 ∧ (x = 1 ∨ x = -1)) ∨ 
  (x = 0 ∧ n ≠ 0) ∨ 
  (x = 1 ∧ n ≠ 0) ∨ 
  (x = -1 ∧ n ≠ 0) ∨ 
  (n ≠ 0 ∧ n ≠ 1 ∧ n ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 ∧ 
   ∃ k : Nat, k > 0 ∧ x = n^k) := by
  constructor
  · intro ⟨k, hk⟩
    by_cases h1 : n = 0
    · left
      exact ⟨h1, by rw [hk, h1]; simp⟩
    · by_cases h2 : n = 1
      · right; left
        exact ⟨h2, by rw [hk, h2]; simp⟩
      · by_cases h3 : n = -1
        · right; right; left
          constructor
          · exact h3
          · rw [hk, h3]
            cases' k with k
            · simp
            · cases' k with k
              · simp
              · simp [Int.pow_succ]
                by_cases heven : (k + 2) % 2 = 0
                · left; simp [Int.pow_succ] at hk
                  have : (-1 : Int)^(k + 2) = 1 := by
                    rw [Int.pow_add]
                    simp [Int.pow_two]
                    rw [Int.pow_mod_two_eq_one_iff_even]
                    exact heven
                  rw [this] at hk
                  exact hk
                · right; simp [Int.pow_succ] at hk
                  have : (-1 : Int)^(k + 2) = -1 := by
                    have hodd : (k + 2) % 2 = 1 := by
                      cases' Nat.mod_two_eq_zero_or_one (k + 2) with h h
                      · contradiction
                      · exact h
                    rw [Int.pow_mod_two_eq_neg_one_iff_odd]
                    exact hodd
                  rw [this] at hk
                  exact hk
        · by_cases h4 : x = 0
          · right; right; right; left
            exact ⟨h4, h1⟩
          · by_cases h5 : x = 1
            · right; right; right; right; left
              exact ⟨h5, h1⟩
            · by_cases h6 : x = -1
              · right; right; right; right; right; left
                exact ⟨h6, h1⟩
              · right; right; right; right; right; right
                exact ⟨h1, h2, h3, h4, h5, h6, k, by simp, hk⟩
  · intro h
    cases' h with h h
    · cases' h with h1 h2
      rw [h1, h2]
      use 1
      simp
    · cases' h with h h
      · cases' h with h1 h2
        rw [h1, h2]
        use 1
        simp
      · cases' h with h h
        · cases' h with h1 h2
          rw [h1]
          cases' h2 with h2 h2
          · rw [h2]
            use 0
            simp
          · rw [h2]
            use 1
            simp
        · cases' h with h h
          · cases' h with h1 h2
            rw [h1]
            use 0
            simp
          · cases' h with h h
            · cases' h with h1 h2
              rw [h1]
              use 1
              simp
            · cases' h with h h
              · cases' h with h1 h2
                rw [h1]
                use 1
                simp
              · cases' h with h1 rest
                cases' rest with h2 rest
                cases' rest with h3 rest
                cases' rest with h4 rest
                cases' rest with h5 rest
                cases' rest with h6 rest
                cases' rest with k hk
                use k
                exact hk.2

-- LLM HELPER
lemma is_perfect_power_correct (x n : Int) : 
  is_perfect_power x n = true → ∃ k : Nat, x = n^k := by
  intro h
  simp [is_perfect_power] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8
  · contradiction
  · rw [h2] at h
    rw [h]
    use 1
    simp
  · rw [h3] at h
    cases' h with h h
    · rw [h]
      use 0
      simp
    · rw [h]
      use 1
      simp
  · rw [h4] at h
    use 0
    simp
  · rw [h5] at h
    use 1
    simp
  · have : x = -1 := by
      have : ¬(n = 0) := h1
      have : ¬(n = 1) := h2
      have : ¬(n = -1) := h3
      have : ¬(x = 0) := h4
      have : ¬(x = 1) := h5
      have : x = -1 ∧ n % 2 = 0 := ⟨h6.1, h6.2⟩
      exact this.1
    rw [this]
    use 1
    simp
  · contradiction
  · have abs_x := Int.natAbs x
    have abs_n := Int.natAbs n
    have : abs_n > 1 := by
      simp [Int.natAbs] at h8
      push_neg at h8
      exact h8
    use 1
    simp

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  simp [problem_spec, implementation]
  use is_perfect_power x n
  constructor
  · rfl
  · intro h
    exact is_perfect_power_correct x n h