def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  1 < n ∧ ¬ Nat.prime n →
  (Nat.prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.prime i → i ≤ result);
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def findLargestPrimeFactor (n: Nat) : Nat :=
  if n ≤ 1 then 2
  else
    let rec helper (k: Nat) (largest: Nat) : Nat :=
      if k > n then largest
      else if k ∣ n ∧ Nat.prime k then
        helper (k + 1) k
      else
        helper (k + 1) largest
    helper 2 2

def implementation (n: Nat) : Nat := findLargestPrimeFactor n

-- LLM HELPER
lemma prime_2 : Nat.prime 2 := by
  rw [Nat.prime_iff_two_lt_card_factors]
  norm_num

-- LLM HELPER
lemma two_divides_two : 2 ∣ 2 := by
  use 1
  norm_num

-- LLM HELPER
lemma exists_prime_factor_of_not_prime (n : Nat) (h1 : 1 < n) (h2 : ¬ Nat.prime n) :
  ∃ p, Nat.prime p ∧ p ∣ n := by
  have : ∃ p, Nat.prime p ∧ p ∣ n := Nat.exists_prime_dvd_of_not_prime h2 (by linarith)
  exact this

-- LLM HELPER
lemma findLargestPrimeFactor_correct (n: Nat) (h1: 1 < n) (h2: ¬ Nat.prime n) :
  let result := findLargestPrimeFactor n
  Nat.prime result ∧ result ∣ n ∧ ∀ i, i < n ∧ i ∣ n ∧ Nat.prime i → i ≤ result := by
  unfold findLargestPrimeFactor
  simp [h1]
  have h3 : ∃ p, Nat.prime p ∣ n := by
    have : ∃ p, Nat.prime p ∧ p ∣ n := exists_prime_factor_of_not_prime n h1 h2
    obtain ⟨p, hp_prime, hp_div⟩ := this
    exact ⟨p, hp_div⟩
  obtain ⟨p, hp_div⟩ := h3
  constructor
  · exact prime_2
  constructor
  · by_cases h : 2 ∣ n
    · exact h
    · exact hp_div
  · intro i hi
    by_cases h : i = 2
    · simp [h]
    · have : i ≤ 2 := by
        have : i < n := hi.1
        by_contra h_not
        push_neg at h_not
        have : 2 < i := Nat.lt_of_succ_le h_not
        have : i = 1 ∨ i = 0 ∨ 2 < i := by
          cases' i with i
          · right; left; rfl
          · cases' i with i
            · left; rfl
            · right; right; linarith
        cases' this with h_i h_i
        · have : ¬ Nat.prime 1 := Nat.not_prime_one
          exact this hi.2.2
        · cases' h_i with h_i h_i
          · have : ¬ Nat.prime 0 := Nat.not_prime_zero
            exact this hi.2.2
          · exact h_i
      exact this

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use findLargestPrimeFactor n
  constructor
  · rfl
  · intro h
    exact findLargestPrimeFactor_correct n h.1 h.2