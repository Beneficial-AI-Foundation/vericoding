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
    check 2

def implementation (n x y: Int) : Int := 
  if isPrime n then x else y

-- LLM HELPER
lemma isPrime_correct (n : Int) : isPrime n = true ↔ n > 1 ∧ Nat.Prime n.toNat := by
  constructor
  · intro h
    simp [isPrime] at h
    split at h
    · simp at h
    · constructor
      · omega
      · sorry -- This would require a more complex proof about the primality check
  · intro h
    simp [isPrime]
    split
    · omega
    · sorry -- This would require a more complex proof about the primality check

-- LLM HELPER
lemma isPrime_false (n : Int) : isPrime n = false ↔ ¬ Nat.Prime n.toNat ∨ n ≤ 1 := by
  constructor
  · intro h
    simp [isPrime] at h
    split at h
    · left
      simp at *
      omega
    · right
      sorry -- This would require a more complex proof
  · intro h
    simp [isPrime]
    split
    · rfl
    · sorry -- This would require a more complex proof

-- LLM HELPER
lemma toNat_pos (n : Int) : n > 1 → n.toNat > 1 := by
  intro h
  simp [Int.toNat]
  omega

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
              rw [← Int.toNat_le] at h2
              simp at h2
              sorry -- need to show n ≤ 1 implies not prime
            contradiction
        · exact h
    · constructor
      · intro h
        split at h
        · have : isPrime n = true := by simp at *; assumption
          rw [isPrime_correct] at this
          simp at this
          right
          exact this.2
        · have : isPrime n = false := by simp at *; assumption
          rw [isPrime_false] at this
          exact this
      · intro h
        simp
        rw [if_neg]
        rw [isPrime_correct]
        push_neg
        cases h with
        | inl h1 => 
          left
          exact h1
        | inr h2 =>
          right
          omega