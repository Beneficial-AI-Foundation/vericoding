import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def decidable_helper (n: Nat) (k: Nat) : Bool :=
  if k * k > n then true
  else if n % k = 0 then false
  else decidable_helper n (k + 1)
termination_by n - k

-- LLM HELPER
def is_prime_decidable (n: Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else decidable_helper n 2

-- LLM HELPER
lemma decidable_helper_correct (n k: Nat) :
  decidable_helper n k = true → ¬ (∃ j, k ≤ j ∧ j < n ∧ n % j = 0) := by
  intro h
  intro ⟨j, hj1, hj2, hj3⟩
  unfold decidable_helper at h
  split_ifs at h with h1 h2
  · exfalso
    cases' Nat.lt_or_ge j k with hcase hcase
    · omega
    · have : j * j ≤ k * k := Nat.mul_le_mul' hcase hcase
      omega
  · simp at h
  · exact decidable_helper_correct n (k + 1) h ⟨j, by omega, hj2, hj3⟩

-- LLM HELPER
lemma decidable_helper_correct_pos (n k: Nat) :
  ¬ (∃ j, k ≤ j ∧ j < n ∧ n % j = 0) → decidable_helper n k = true := by
  intro h
  unfold decidable_helper
  split_ifs with h1 h2
  · rfl
  · exfalso
    apply h
    use k
    constructor
    · exact le_refl k
    constructor
    · by_contra h_contra
      have : k * k ≤ n := Nat.le_of_not_gt h1
      exact h_contra this
    · exact h2
  · apply decidable_helper_correct_pos n (k + 1)
    intro ⟨j, hj1, hj2, hj3⟩
    apply h
    use j
    exact ⟨Nat.le_trans (Nat.le_succ k) hj1, hj2, hj3⟩

-- LLM HELPER
lemma is_prime_decidable_correct (n: Nat) :
  is_prime_decidable n = true ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0) := by
  constructor
  · intro h
    intro ⟨k, hk⟩
    unfold is_prime_decidable at h
    cases' Nat.lt_or_ge n 2 with h1 h1
    · simp [h1] at h
    · cases' Nat.eq_or_lt_of_le h1 with h2 h2
      · rw [h2] at hk
        omega
      · simp [h1, h2] at h
        have := decidable_helper_correct n 2 h
        exact this ⟨k, by omega, hk.2.1, hk.2.2⟩
  · intro h
    unfold is_prime_decidable
    cases' Nat.lt_or_ge n 2 with h1 h1
    · simp [h1]
    · cases' Nat.eq_or_lt_of_le h1 with h2 h2
      · simp [h2]
      · simp [h1, h2]
        apply decidable_helper_correct_pos n 2
        intro ⟨j, hj1, hj2, hj3⟩
        apply h
        use j
        exact ⟨by omega, hj2, hj3⟩

def implementation (s: String) : Bool := is_prime_decidable s.length

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use is_prime_decidable s.length
  constructor
  · rfl
  · exact is_prime_decidable_correct s.length