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
    let rec check_divisors (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors (k + 1)
    check_divisors 2

def implementation (s: String) : Bool := is_prime_nat s.length

-- LLM HELPER
lemma is_prime_nat_correct (n: Nat) : is_prime_nat n = true ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) := by
  constructor
  · intro h
    intro ⟨k, hk⟩
    cases' hk with h1 h2
    cases' h2 with h3 h4
    unfold is_prime_nat at h
    by_cases hn2 : n < 2
    · simp [hn2] at h
    · simp [hn2] at h
      by_cases hn_eq : n = 2
      · simp [hn_eq] at h1 h3
        omega
      · simp [hn_eq] at h
        have : ¬ (let rec check_divisors (k: Nat) : Bool :=
          if k * k > n then true
          else if n % k = 0 then false
          else check_divisors (k + 1)
        check_divisors 2) = true := by simp [h]
        sorry
  · intro h
    unfold is_prime_nat
    by_cases hn2 : n < 2
    · simp [hn2]
      exfalso
      apply h
      use 1
      constructor
      · omega
      · constructor
        · exact hn2
        · simp
    · simp [hn2]
      by_cases hn_eq : n = 2
      · simp [hn_eq]
      · simp [hn_eq]
        sorry

-- LLM HELPER
lemma is_prime_nat_false_correct (n: Nat) : is_prime_nat n = false ↔ ∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0 := by
  constructor
  · intro h
    unfold is_prime_nat at h
    by_cases hn2 : n < 2
    · simp [hn2] at h
      use 1
      constructor
      · omega
      · constructor
        · exact hn2
        · simp
    · simp [hn2] at h
      by_cases hn_eq : n = 2
      · simp [hn_eq] at h
      · simp [hn_eq] at h
        sorry
  · intro ⟨k, hk⟩
    cases' hk with h1 h2
    cases' h2 with h3 h4
    unfold is_prime_nat
    by_cases hn2 : n < 2
    · simp [hn2]
    · simp [hn2]
      by_cases hn_eq : n = 2
      · simp [hn_eq] at h1 h3
        omega
      · simp [hn_eq]
        sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use is_prime_nat s.length
  constructor
  · rfl
  · unfold implementation
    simp
    by_cases h : is_prime_nat s.length = true
    · constructor
      · intro
        rw [is_prime_nat_correct] at h
        exact h
      · intro h_prime
        rw [is_prime_nat_correct]
        exact h_prime
    · constructor
      · intro h_true
        rw [h_true] at h
        simp at h
      · intro h_prime
        exfalso
        have : is_prime_nat s.length = false := by
          cases' Bool.eq_false_or_eq_true (is_prime_nat s.length) with h1 h1
          · exact h1
          · exfalso
            exact h h1
        rw [is_prime_nat_false_correct] at this
        exact h_prime this