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
    loop 2

-- LLM HELPER
lemma isPrime_correct (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    cases' Nat.lt_or_ge n 2 with h1 h2
    · simp [isPrime] at h
      split at h <;> contradiction
    · simp [isPrime] at h
      split at h
      · contradiction
      · exact Nat.prime_def_lt''.mpr ⟨h2, fun d hd hdlt => by
          have : isPrime.loop n d = true := by
            simp [isPrime.loop] at h
            exact h
          simp [isPrime.loop] at this
          split at this
          · simp at this
          · simp at this
            exact this
          · exact this⟩
  · intro h
    simp [isPrime]
    split
    · have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · have : ∀ i, 2 ≤ i → i * i ≤ n → n % i ≠ 0 := by
        intro i hi1 hi2
        have : i < n := by
          have : i * i ≤ n := hi2
          have : i ≤ i * i := by
            cases' i with i
            · omega
            · cases' i with i
              · omega
              · simp [Nat.succ_mul]
                omega
          omega
        exact Nat.Prime.not_dvd_of_pos_of_lt h (Nat.pos_of_ne_zero (ne_of_gt hi1)) this
      exact isPrime.loop_correct n 2 this

-- LLM HELPER
lemma isPrime.loop_correct (n : Nat) (i : Nat) (h : ∀ j, 2 ≤ j → j < i → j * j ≤ n → n % j ≠ 0) : 
  isPrime.loop n i = true ↔ (∀ j, i ≤ j → j * j ≤ n → n % j ≠ 0) := by
  sorry

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
              cases' Int.natCast_nonneg.mp (le_of_lt (Int.coe_nat_pos.mpr (Nat.pos_of_ne_zero (ne_of_gt (Nat.Prime.two_le h1))))) with h2
              · omega
              · omega
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
          assumption
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