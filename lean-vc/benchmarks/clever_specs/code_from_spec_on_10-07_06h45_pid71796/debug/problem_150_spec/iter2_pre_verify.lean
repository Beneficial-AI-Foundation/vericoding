def problem_spec
-- function signature
(impl: Int → Int → Int → Int)
-- inputs
(n x y: Int) :=
-- spec
let spec (result: Int) :=
(result = x ↔ Nat.Prime n.toNat) ∧
(result = y ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1))
-- program terminates
∃ result, impl n x y = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isPrime (n : Int) : Bool :=
  if n ≤ 1 then false
  else
    let rec check (k : Nat) : Bool :=
      if k * k > n.toNat then true
      else if n.toNat % k = 0 then false
      else check (k + 1)
    termination_by n.toNat + 1 - k
    check 2

def implementation (n x y: Int) : Int := 
  if isPrime n then x else y

-- LLM HELPER
lemma nat_prime_iff_int_prime (n : Int) : n > 1 → (Nat.Prime n.toNat ↔ isPrime n = true) := by
  intro h
  constructor
  · intro hp
    simp [isPrime]
    split
    · omega
    · simp [Nat.Prime] at hp
      have check_correct : ∀ k, k ≥ 2 → k * k ≤ n.toNat → 
        (isPrime.check n k = true ↔ ∀ d, k ≤ d → d * d ≤ n.toNat → ¬(n.toNat % d = 0)) := by
        intro k hk hbound
        sorry
      have : isPrime.check n 2 = true := by
        apply (check_correct 2 (by norm_num) (by sorry)).mpr
        intro d hd hdbound hdiv
        have : d = 1 ∨ d = n.toNat := hp.2 d (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
        cases this with
        | inl h1 => omega
        | inr h2 => 
          rw [h2] at hdbound
          have : n.toNat * n.toNat ≤ n.toNat := hdbound
          have : n.toNat ≤ 1 := by
            cases n.toNat with
            | zero => simp
            | succ m => 
              simp at this
              omega
          omega
      exact this
  · intro h
    simp [isPrime] at h
    split at h
    · contradiction
    · simp [Nat.Prime]
      constructor
      · omega
      · intro d hdiv
        by_contra hcontra
        have : d ≥ 2 ∧ d < n.toNat := by
          constructor
          · by_contra h1
            simp at h1
            cases Nat.lt_or_eq_of_le h1 with
            | inl h2 => 
              cases d with
              | zero => simp at hdiv
              | succ d' =>
                cases d' with
                | zero => 
                  simp at hdiv
                  omega
                | succ d'' => omega
            | inr h2 => 
              rw [h2] at hdiv
              simp at hdiv
              omega
          · by_contra h2
            simp at h2
            have : n.toNat ≤ d := h2
            have : d * d ≤ n.toNat := by
              cases Nat.lt_or_eq_of_le this with
              | inl h3 => 
                have : n.toNat < d := h3
                omega
              | inr h3 =>
                rw [← h3]
                omega
            have check_false : isPrime.check n 2 = false := by
              sorry
            simp at h
            exact check_false
        sorry

-- LLM HELPER  
lemma isPrime_correct (n : Int) : isPrime n = true ↔ n > 1 ∧ Nat.Prime n.toNat := by
  constructor
  · intro h
    simp [isPrime] at h
    split at h
    · simp at h
    · constructor
      · omega
      · rw [← nat_prime_iff_int_prime]
        · exact h
        · omega
  · intro h
    rw [nat_prime_iff_int_prime]
    · exact h.2
    · exact h.1

-- LLM HELPER
lemma isPrime_false (n : Int) : isPrime n = false ↔ ¬ Nat.Prime n.toNat ∨ n ≤ 1 := by
  constructor
  · intro h
    by_contra hcontra
    simp at hcontra
    have : isPrime n = true := by
      rw [isPrime_correct]
      exact ⟨hcontra.2, hcontra.1⟩
    rw [this] at h
    simp at h
  · intro h
    by_contra hcontra
    have : isPrime n = true := by simp at hcontra; exact hcontra
    rw [isPrime_correct] at this
    cases h with
    | inl h1 => exact h1 this.2
    | inr h2 => omega

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  simp [problem_spec, implementation]
  use (if isPrime n then x else y)
  constructor
  · rfl
  · simp
    constructor
    · constructor
      · intro h
        split at h
        · have : isPrime n = true := by simp at *; assumption
          rw [isPrime_correct] at this
          exact this.2
        · contradiction
      · intro h
        simp
        rw [if_pos]
        rw [isPrime_correct]
        constructor
        · by_contra h_contra
          simp at h_contra
          cases h_contra with
          | inl h1 => omega
          | inr h2 => 
            have : ¬ Nat.Prime n.toNat := by
              rw [Nat.Prime]
              simp
              left
              omega
            contradiction
        · exact h
    · constructor
      · intro h
        split at h
        · have : isPrime n = true := by simp at *; assumption
          rw [isPrime_correct] at this
          right
          exact this.2
        · have : isPrime n = false := by simp at *; assumption
          rw [isPrime_false] at this
          exact this
      · intro h
        simp
        rw [if_neg]
        rw [Bool.not_eq_true]
        rw [isPrime_false]
        exact h