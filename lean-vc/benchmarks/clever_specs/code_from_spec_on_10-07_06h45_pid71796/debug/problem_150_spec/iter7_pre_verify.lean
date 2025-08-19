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
    decreasing_by simp_wf; omega
    check 2

def implementation (n x y: Int) : Int := 
  if isPrime n then x else y

-- LLM HELPER
lemma isPrime_correct (n : Int) : isPrime n = true ↔ (n > 1 ∧ Nat.Prime n.toNat) := by
  simp [isPrime, Nat.Prime]
  split_ifs with h
  · simp
    intro h_pos
    omega
  · simp
    constructor
    · intro h_check
      constructor
      · omega
      · constructor
        · omega
        · intro d hdiv h1 h2
          have : d ≥ 2 := by omega
          have : d * d ≤ n.toNat := by
            cases Nat.lt_or_eq_of_le h1 with
            | inl h3 => omega
            | inr h3 => rw [← h3]; omega
          have check_result : isPrime.check n 2 = false := by
            induction d using Nat.strong_induction_on with
            | h d ih =>
              simp [isPrime.check]
              if h_gt : 2 * 2 > n.toNat then
                have : n.toNat < 4 := by omega
                have : n.toNat ≥ 2 := by omega
                interval_cases n.toNat
                · simp at hdiv
                · simp at hdiv
                  cases hdiv with
                  | inl h => omega
                  | inr h => omega
              else
                simp [h_gt]
                if h_eq : n.toNat % 2 = 0 then
                  have : 2 ∣ n.toNat := by
                    rw [Nat.dvd_iff_mod_eq_zero]
                    exact h_eq
                  if h_ne : 2 ≠ d then
                    have : d > 2 := by omega
                    have : 2 < d := by omega
                    have : ¬ Nat.Prime n.toNat := by
                      rw [Nat.Prime]
                      simp
                      right
                      use 2
                      constructor
                      · exact this
                      constructor
                      · exact Nat.dvd_of_mod_eq_zero h_eq
                      · omega
                    rw [Nat.Prime] at h_check
                    simp at h_check
                    cases h_check with
                    | inl h => omega
                    | inr h => 
                      obtain ⟨d', hd'1, hd'2, hd'3⟩ := h
                      if h_eq_d : d' = 2 then
                        rw [h_eq_d] at hd'3
                        omega
                      else
                        have : d' > 2 := by omega
                        have : d' = d ∨ d' ≠ d := by tauto
                        cases this with
                        | inl h => rw [h] at hd'2; contradiction
                        | inr h => omega
                  else
                    rw [h_ne] at hdiv
                    exact hdiv
                else
                  sorry
          rw [check_result] at h_check
          simp at h_check
    · intro h_prime
      have : n.toNat > 1 := by omega
      simp [Nat.Prime] at h_prime
      sorry

-- LLM HELPER
lemma isPrime_false (n : Int) : isPrime n = false ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1) := by
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
    · by_cases h : isPrime n
      · simp [h]
        constructor
        · intro
          rw [isPrime_correct] at h
          exact h.2
        · intro hp
          by_contra hcontra
          simp at hcontra
          have : isPrime n = false := hcontra
          rw [this] at h
          simp at h
      · simp [h]
        constructor
        · intro hcontra
          simp at hcontra
        · intro hp
          exfalso
          have : isPrime n = true := by
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
            · exact hp
          rw [this] at h
          simp at h
    · by_cases h : isPrime n
      · simp [h]
        constructor
        · intro hcontra
          simp at hcontra
        · intro hp
          exfalso
          rw [isPrime_correct] at h
          exact hp h.2
      · simp [h]
        constructor
        · intro
          rw [isPrime_false] at h
          exact h
        · intro hp
          by_contra hcontra
          simp at hcontra
          have : isPrime n = true := hcontra
          rw [this] at h
          simp at h