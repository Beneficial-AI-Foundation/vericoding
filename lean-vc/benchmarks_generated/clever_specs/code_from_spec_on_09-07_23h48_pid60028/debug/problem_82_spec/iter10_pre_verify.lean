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
    decreasing_by {
      simp_wf
      have h1 : k * k ≤ n := by
        by_contra h
        simp at h
        exact h
      have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h2]
      omega
    }
    check_divisors n 2

def implementation (s: String) : Bool := is_prime_nat s.length

-- LLM HELPER
lemma check_divisors_sound (n k: Nat) : 
  (let rec check_divisors (n: Nat) (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors n (k + 1)
    termination_by n - k * k
    decreasing_by {
      simp_wf
      have h1 : k * k ≤ n := by
        by_contra h
        simp at h
        exact h
      have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h2]
      omega
    }
    check_divisors n k) = false → 
  ∃ d, k ≤ d ∧ d * d ≤ n ∧ n % d = 0 := by
  intro h
  unfold check_divisors at h
  by_cases h1 : k * k > n
  · simp [h1] at h
  · simp [h1] at h
    by_cases h2 : n % k = 0
    · simp [h2] at h
      use k
      constructor
      · le_refl k
      constructor
      · omega
      · exact h2
    · simp [h2] at h
      have ih := check_divisors_sound n (k + 1) h
      obtain ⟨d, hd1, hd2, hd3⟩ := ih
      use d
      constructor
      · omega
      · exact ⟨hd2, hd3⟩

-- LLM HELPER
lemma check_divisors_complete (n k: Nat) : 
  (∃ d, k ≤ d ∧ d * d ≤ n ∧ n % d = 0) →
  (let rec check_divisors (n: Nat) (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors n (k + 1)
    termination_by n - k * k
    decreasing_by {
      simp_wf
      have h1 : k * k ≤ n := by
        by_contra h
        simp at h
        exact h
      have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h2]
      omega
    }
    check_divisors n k) = false := by
  intro ⟨d, hd1, hd2, hd3⟩
  unfold check_divisors
  by_cases h1 : k * k > n
  · simp [h1]
    have : d * d ≤ n := hd2
    have : k ≤ d := hd1
    have : k * k ≤ d * d := by
      apply Nat.mul_le_mul'
      exact hd1
      exact hd1
    omega
  · simp [h1]
    by_cases h2 : n % k = 0
    · simp [h2]
    · simp [h2]
      apply check_divisors_complete
      by_cases hkd : k = d
      · rw [hkd] at h2
        contradiction
      · use d
        constructor
        · have : k < d := Nat.lt_of_le_of_ne hd1 hkd
          omega
        · exact ⟨hd2, hd3⟩

-- LLM HELPER
lemma is_prime_nat_correct (n: Nat) : 
  is_prime_nat n = true ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) := by
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
        have hk_sq : k * k ≤ n ∨ k * k > n := le_or_gt (k * k) n
        cases hk_sq with
        | inl h_le =>
          have : ∃ d, 2 ≤ d ∧ d * d ≤ n ∧ n % d = 0 := ⟨k, h2k, h_le, hdiv⟩
          have : check_divisors n 2 = false := by
            apply check_divisors_complete
            exact ⟨k, h2k, h_le, hdiv⟩
          simp at this
          rw [this] at h
          contradiction
        | inr h_gt =>
          have hsqrt : ∃ d, d * d ≤ n ∧ n % d = 0 ∧ d ≥ 2 := by
            have : n = k * (n / k) + (n % k) := Nat.div_add_mod n k
            rw [hdiv] at this
            simp at this
            have : n = k * (n / k) := this
            have : n / k ≥ 2 := by
              by_contra h_contra
              simp at h_contra
              interval_cases (n / k)
              · simp at this
                omega
              · rw [this]
                simp
                omega
            have : n / k < k := by
              by_contra h_contra
              simp at h_contra
              have : k * (n / k) ≥ k * k := Nat.mul_le_mul_left k h_contra
              rw [← this] at h_gt
              simp at h_gt
            use n / k
            constructor
            · have : n / k * (n / k) ≤ n / k * k := Nat.mul_le_mul_left (n / k) (le_of_lt this)
              rw [← this]
              exact le_refl n
            constructor
            · rw [← this]
              simp
            · exact this
          obtain ⟨d, hd1, hd2, hd3⟩ := hsqrt
          have : check_divisors n 2 = false := by
            apply check_divisors_complete
            exact ⟨d, hd3, hd1, hd2⟩
          simp at this
          rw [this] at h
          contradiction
  · intro h
    unfold is_prime_nat
    by_cases hn2 : n < 2
    · simp [hn2]
    · simp [hn2]
      by_cases hn_eq : n = 2
      · simp [hn_eq]
      · simp [hn_eq]
        by_contra h_contra
        simp at h_contra
        have : ∃ d, 2 ≤ d ∧ d * d ≤ n ∧ n % d = 0 := check_divisors_sound n 2 h_contra
        obtain ⟨d, hd1, hd2, hd3⟩ := this
        have : d < n := by
          by_contra h_not_lt
          simp at h_not_lt
          have : d * d ≥ n * n := by
            apply Nat.mul_le_mul'
            exact h_not_lt
            exact h_not_lt
          have : n ≥ 2 := by omega
          have : n * n ≥ n * 2 := Nat.mul_le_mul_left n this
          have : n * 2 ≥ 2 * 2 := by
            apply Nat.mul_le_mul_right
            exact this
          omega
        apply h
        use d
        exact ⟨hd1, this, hd3⟩

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