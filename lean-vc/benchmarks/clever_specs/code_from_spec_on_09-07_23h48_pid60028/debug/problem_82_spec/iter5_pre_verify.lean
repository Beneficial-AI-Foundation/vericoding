def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
let is_prime (n: Nat) : Prop :=
  ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
  result ↔ is_prime s.length
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def is_prime_nat (n: Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else
    let rec check_divisors (n: Nat) (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors n (k + 1)
    termination_by n - k * k
    check_divisors n 2

def implementation (s: String) : Bool := is_prime_nat s.length

-- LLM HELPER
lemma is_prime_nat_correct (n: Nat) : is_prime_nat n = true ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) := by
  constructor
  · intro h
    intro ⟨k, h2k, hkn, hdiv⟩
    unfold is_prime_nat at h
    by_cases hn2 : n < 2
    · simp [hn2] at h
    · simp [hn2] at h
      by_cases hn_eq : n = 2
      · simp [hn_eq] at h2k hkn
        omega
      · simp [hn_eq] at h
        have check_true : (let rec check_divisors (n: Nat) (k: Nat) : Bool :=
          if k * k > n then true
          else if n % k = 0 then false
          else check_divisors n (k + 1)
        termination_by n - k * k
        check_divisors n 2) = true := h
        have h_div : ∀ j, 2 ≤ j → j * j ≤ n → n % j ≠ 0 := by
          intro j hj2 hjn
          have : j < n := by
            by_contra h_not
            simp at h_not
            have : j * j ≥ n := by
              have : j ≥ n := h_not
              have : j * j ≥ n * n := by
                apply Nat.mul_le_mul'
                exact h_not
                exact h_not
              have : n * n ≥ n := by
                cases' n with n
                · simp
                · simp
                  apply Nat.mul_le_mul_right
                  omega
              omega
            omega
          have : j * j ≤ n := hjn
          have : j < n := by omega
          by_contra h_div_zero
          have : n % j = 0 := by simp at h_div_zero; exact h_div_zero
          have : ∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0 := ⟨j, hj2, this, this⟩
          exact h ⟨j, hj2, this, this⟩
        have : n % k = 0 := hdiv
        have : 2 ≤ k := h2k
        have : k < n := hkn
        have : k * k ≤ n := by
          by_contra h_not
          simp at h_not
          have : k * k > n := h_not
          exact h_div k h2k (by omega)
        have : n % k ≠ 0 := h_div k h2k this
        exact this hdiv
  · intro h
    unfold is_prime_nat
    by_cases hn2 : n < 2
    · simp [hn2]
      intro k h2k hkn
      omega
    · simp [hn2]
      by_cases hn_eq : n = 2
      · simp [hn_eq]
        intro k h2k hkn
        omega
      · simp [hn_eq]
        have h_no_div : ∀ j, 2 ≤ j → j * j ≤ n → n % j ≠ 0 := by
          intro j hj2 hjn
          by_contra h_div_zero
          simp at h_div_zero
          have : j < n := by
            by_contra h_not
            simp at h_not
            have : j * j ≥ n * n := by
              apply Nat.mul_le_mul'
              exact h_not
              exact h_not
            have : n * n ≥ n := by
              cases' n with n
              · simp
              · simp
                apply Nat.mul_le_mul_right
                omega
            omega
          have : ∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0 := ⟨j, hj2, this, h_div_zero⟩
          exact h this
        have check_result : (let rec check_divisors (n: Nat) (k: Nat) : Bool :=
          if k * k > n then true
          else if n % k = 0 then false
          else check_divisors n (k + 1)
        termination_by n - k * k
        check_divisors n 2) = true := by
          have : ∀ k, 2 ≤ k → (let rec check_divisors (n: Nat) (k: Nat) : Bool :=
            if k * k > n then true
            else if n % k = 0 then false
            else check_divisors n (k + 1)
          termination_by n - k * k
          check_divisors n k) = true := by
            intro k hk
            induction k using Nat.strong_induction_on with
            | ind k ih =>
              simp only [check_divisors]
              by_cases h_sq : k * k > n
              · simp [h_sq]
              · simp [h_sq]
                by_cases h_div : n % k = 0
                · simp [h_div]
                  have : k * k ≤ n := by omega
                  have : n % k ≠ 0 := h_no_div k hk this
                  exact this h_div
                · simp [h_div]
                  apply ih
                  · omega
                  · omega
          exact this 2 (by norm_num)
        exact check_result

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use is_prime_nat s.length
  constructor
  · rfl
  · unfold implementation
    simp
    rw [is_prime_nat_correct]