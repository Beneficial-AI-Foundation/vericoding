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
        have : k * k > n := h
        contradiction
      have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h2]
      omega
    }
    check_divisors n 2

def implementation (s: String) : Bool := is_prime_nat s.length

-- LLM HELPER
lemma check_divisors_correct (n k: Nat) (hk: k ≥ 2) (hn: n ≥ 2) : 
  (∃ d, k ≤ d ∧ d * d ≤ n ∧ n % d = 0) ↔ 
  ¬(let rec check_divisors (n: Nat) (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors n (k + 1)
    termination_by n - k * k
    decreasing_by {
      simp_wf
      have h1 : k * k ≤ n := by
        by_contra h
        simp at h
        have : k * k > n := h
        contradiction
      have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h2]
      omega
    }
    check_divisors n k) := by
  sorry

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
          sorry
        | inr h_gt =>
          have : n < k * k := h_gt
          have : k * k ≤ k * k := le_refl _
          have : n < k * k := h_gt
          have : k ≥ 2 := h2k
          have : k ≥ Nat.sqrt n + 1 := by
            have : k * k > n := h_gt
            sorry
          sorry
  · intro h
    unfold is_prime_nat
    by_cases hn2 : n < 2
    · simp [hn2]
    · simp [hn2]
      by_cases hn_eq : n = 2
      · simp [hn_eq]
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
    rw [is_prime_nat_correct]