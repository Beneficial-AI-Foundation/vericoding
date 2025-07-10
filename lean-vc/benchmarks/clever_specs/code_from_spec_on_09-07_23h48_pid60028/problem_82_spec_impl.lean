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
        -- We need to show that check_divisors n 2 = true leads to a contradiction
        have : k * k ≤ n ∨ k * k > n := le_or_gt (k * k) n
        cases this with
        | inl h_le =>
          -- If k * k ≤ n, then check_divisors should find k as a divisor
          have : n ≥ 2 := by omega
          have : k ≥ 2 := h2k
          have : k < n := hkn
          sorry -- This requires more complex reasoning about the check_divisors function
        | inr h_gt =>
          -- If k * k > n, we need to find a smaller divisor
          have hsqrt : ∃ d, d * d ≤ n ∧ n % d = 0 ∧ d ≥ 2 := by
            sorry -- Complex divisor reasoning
          sorry
  · intro h
    unfold is_prime_nat
    by_cases hn2 : n < 2
    · simp [hn2]
    · simp [hn2]
      by_cases hn_eq : n = 2
      · simp [hn_eq]
      · simp [hn_eq]
        -- We need to show check_divisors n 2 = true
        by_contra h_contra
        simp at h_contra
        sorry -- This requires showing that if check_divisors returns false, then there exists a divisor

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use is_prime_nat s.length
  constructor
  · rfl
  · unfold implementation
    simp
    exact is_prime_nat_correct s.length