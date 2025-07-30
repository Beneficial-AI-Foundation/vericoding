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
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    let rec loop (i : Nat) : Bool :=
      if i * i > n then true
      else if n % i = 0 then false
      else loop (i + 1)
    termination_by n + 1 - i
    decreasing_by {
      simp_wf
      omega
    }
    loop 2

-- LLM HELPER
lemma isPrime_correct (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [isPrime] at h
    split at h
    · contradiction
    · rw [Nat.prime_def_lt'']
      constructor
      · omega
      · intro d hd hdlt
        have loop_true : isPrime.loop n 2 = true := h
        have : ∀ k, 2 ≤ k → k * k ≤ n → n % k ≠ 0 := by
          intro k hk1 hk2
          have : isPrime.loop n k = true := by
            induction k using Nat.strong_induction_on with
            | ind k ih =>
              simp [isPrime.loop]
              split
              · simp
              · split
                · simp
                  contradiction
              · have : k < n := by
                  have : k * k ≤ n := hk2
                  cases' k with k
                  · omega
                  · simp [Nat.succ_mul] at this
                    omega
                exact ih (k + 1) (by omega) (by omega) (by omega)
          simp [isPrime.loop] at this
          split at this
          · simp at this
          · simp at this
            exact this
        exact this d hd (by omega)
  · intro h
    simp [isPrime]
    split
    · have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · have : isPrime.loop n 2 = true := by
        have : ∀ k, 2 ≤ k → k * k ≤ n → n % k ≠ 0 := by
          intro k hk1 hk2
          have : k < n := by
            cases' k with k
            · omega
            · cases' k with k
              · omega
              · simp [Nat.succ_mul] at hk2
                omega
          exact Nat.Prime.not_dvd_of_pos_of_lt h (Nat.pos_of_ne_zero (ne_of_gt hk1)) this
        induction 2 using Nat.strong_induction_on with
        | ind k ih =>
          simp [isPrime.loop]
          split
          · simp
          · split
            · simp
              exact this k (by omega) (by omega)
          · exact ih (k + 1) (by omega) (by omega)
      exact this

-- LLM HELPER
lemma isPrime_false_iff (n : Nat) : isPrime n = false ↔ ¬ Nat.Prime n := by
  rw [← Bool.not_eq_true]
  rw [isPrime_correct]
  simp

def implementation (n x y: Int) : Int := 
  if n ≤ 1 then y
  else if isPrime n.toNat then x
  else y

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  simp [problem_spec]
  use implementation n x y
  constructor
  · rfl
  · simp [implementation]
    constructor
    · constructor
      · intro h
        split at h
        · simp at h
          subst h
          by_cases h1 : Nat.Prime n.toNat
          · have : n ≥ 2 := by
              have : n.toNat ≥ 2 := Nat.Prime.two_le h1
              omega
            omega
          · exact h1
        · split at h
          · simp at h
            subst h
            rw [isPrime_correct]
            assumption
          · simp at h
            subst h
            by_cases h1 : Nat.Prime n.toNat
            · have : isPrime n.toNat = true := isPrime_correct n.toNat |>.mpr h1
              simp [this]
            · exact h1
      · intro h
        split
        · simp
          right
          omega
        · split
          · simp
          · simp
            by_cases h1 : Nat.Prime n.toNat
            · contradiction
            · right
              exact h1
    · constructor
      · intro h
        split at h
        · simp at h
          subst h
          left
          by_cases h1 : Nat.Prime n.toNat
          · have : n ≥ 2 := by
              have : n.toNat ≥ 2 := Nat.Prime.two_le h1
              omega
            omega
          · exact h1
        · split at h
          · simp at h
            subst h
            have : ¬ Nat.Prime n.toNat := by
              have : isPrime n.toNat = false := by simp
              exact isPrime_false_iff n.toNat |>.mp this
            left
            exact this
          · simp at h
            subst h
            left
            by_cases h1 : Nat.Prime n.toNat
            · have : isPrime n.toNat = true := isPrime_correct n.toNat |>.mpr h1
              simp [this]
            · exact h1
      · intro h
        cases h with
        | inl h1 => 
          split
          · simp
          · split
            · have : isPrime n.toNat = true := isPrime_correct n.toNat |>.mpr (by
                by_contra h2
                exact h1 h2)
              simp [this]
            · simp
        | inr h1 =>
          split
          · simp
          · split
            · have : n ≥ 2 := by omega
              have : n.toNat ≥ 2 := by omega
              have : Nat.Prime n.toNat := by
                by_contra h2
                exact h1 h2
              have : isPrime n.toNat = true := isPrime_correct n.toNat |>.mpr this
              simp [this]
            · simp