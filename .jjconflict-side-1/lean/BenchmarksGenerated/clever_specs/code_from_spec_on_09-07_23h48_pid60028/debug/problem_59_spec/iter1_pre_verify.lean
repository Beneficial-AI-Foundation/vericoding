def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  1 < n ∧ ¬ Nat.Prime n →
  (Nat.Prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result);
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def findLargestPrimeFactor (n: Nat) : Nat :=
  if n ≤ 1 then 2
  else
    let rec helper (k: Nat) (largest: Nat) : Nat :=
      if k > n then largest
      else if k ∣ n ∧ Nat.Prime k then
        helper (k + 1) k
      else
        helper (k + 1) largest
    helper 2 2

def implementation (n: Nat) : Nat := findLargestPrimeFactor n

-- LLM HELPER
lemma prime_2 : Nat.Prime 2 := by
  rw [Nat.Prime]
  constructor
  · norm_num
  · intro m hm
    interval_cases m
    · left; rfl
    · right; rfl

-- LLM HELPER
lemma two_divides_two : 2 ∣ 2 := by
  use 1
  norm_num

-- LLM HELPER  
lemma helper_finds_largest_prime_factor (n k largest: Nat) (h1: k ≤ n) (h2: Nat.Prime largest) (h3: largest ∣ n) 
  (h4: ∀ i, i < k ∧ i ∣ n ∧ Nat.Prime i → i ≤ largest) :
  let result := findLargestPrimeFactor.helper n k largest
  Nat.Prime result ∧ result ∣ n ∧ ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result := by
  sorry

-- LLM HELPER
lemma findLargestPrimeFactor_correct (n: Nat) (h1: 1 < n) (h2: ¬ Nat.Prime n) :
  let result := findLargestPrimeFactor n
  Nat.Prime result ∧ result ∣ n ∧ ∀ i, i < n ∧ i ∣ n ∧ Nat.Prime i → i ≤ result := by
  unfold findLargestPrimeFactor
  simp [h1]
  have h3 : ∃ p, Nat.Prime p ∧ p ∣ n := by
    have : ∃ p, Nat.Prime p ∧ p ∣ n := Nat.exists_prime_dvd_of_not_prime h2 (by linarith)
    exact this
  obtain ⟨p, hp_prime, hp_div⟩ := h3
  have h4 : 2 ≤ n := by linarith
  constructor
  · have : Nat.Prime 2 := prime_2
    exact this
  constructor
  · have : 2 ∣ n ∨ ∃ q, Nat.Prime q ∧ q ∣ n ∧ q ≠ 2 := by
      by_cases h : 2 ∣ n
      · left; exact h
      · right; use p; exact ⟨hp_prime, hp_div, by
          intro h_eq
          rw [h_eq] at hp_div
          contradiction⟩
    cases this with
    | inl h => exact h
    | inr h => obtain ⟨q, hq_prime, hq_div, _⟩ := h; exact hq_div
  · intro i hi
    sorry

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use findLargestPrimeFactor n
  constructor
  · rfl
  · intro h
    exact findLargestPrimeFactor_correct n h.1 h.2