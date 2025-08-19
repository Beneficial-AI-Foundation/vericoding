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
  simp [isPrime]
  split
  · simp
    intro h
    omega
  · simp
    constructor
    · intro h
      constructor
      · omega
      · simp [Nat.Prime]
        constructor
        · omega
        · intro d hdiv h1 h2
          have : d ≥ 2 := by omega
          have : d * d ≤ n.toNat := by
            cases Nat.lt_or_eq_of_le h1 with
            | inl h3 => omega
            | inr h3 => rw [← h3]; omega
          have check_result : isPrime.check n 2 = false := by
            simp [isPrime.check]
            sorry
          rw [check_result] at h
          simp at h
    · intro h
      have : n.toNat > 1 := by omega
      simp [Nat.Prime] at h
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