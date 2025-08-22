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
      have h1 : i * i ≤ n := by
        by_contra h
        simp at h
        exact h
      omega
    }
    loop 2

-- LLM HELPER
lemma isPrime_correct (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    sorry
  · intro h
    sorry

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
              have : ¬ isPrime n.toNat = true := by simp [this]
              rw [isPrime_correct] at this
              exact this
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