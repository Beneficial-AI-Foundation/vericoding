def problem_spec
-- function signature
(implementation: Nat → Bool)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Bool) :=
  result ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def has_divisor_in_range (n: Nat) (start: Nat) (stop: Nat) : Bool :=
  if start ≥ stop then false
  else if n % start = 0 then true
  else has_divisor_in_range n (start + 1) stop

def implementation (n: Nat): Bool := 
  if n < 2 then false
  else ¬ has_divisor_in_range n 2 n

-- LLM HELPER
lemma has_divisor_in_range_spec (n start stop: Nat) :
  has_divisor_in_range n start stop = true ↔ 
  ∃ k, start ≤ k ∧ k < stop ∧ n % k = 0 := by
  induction stop using Nat.strong_induction_on generalizing start with
  | ind stop ih =>
    simp [has_divisor_in_range]
    by_cases h1 : start ≥ stop
    · simp [h1]
      constructor
      · intro h_false
        exact False.elim h_false
      · intro ⟨k, hk⟩
        have : k < stop := hk.2.1
        have : k ≥ start := hk.1
        have : start ≤ k := hk.1
        have : k < stop := hk.2.1
        have : start < stop := Nat.lt_of_le_of_lt hk.1 hk.2.1
        exact Nat.not_le.mpr this h1
    · simp [h1]
      by_cases h2 : n % start = 0
      · simp [h2]
        constructor
        · intro _
          exact ⟨start, Nat.le_refl start, Nat.lt_of_not_ge h1, h2⟩
        · intro _
          trivial
      · simp [h2]
        rw [ih (start + 1)]
        constructor
        · intro ⟨k, hk⟩
          exact ⟨k, Nat.le_trans (Nat.le_succ start) hk.1, hk.2.1, hk.2.2⟩
        · intro ⟨k, hk⟩
          by_cases h3 : k = start
          · rw [h3] at hk
            exact False.elim (h2 hk.2.2)
          · have : start < k := Nat.lt_of_le_of_ne hk.1 h3
            have : start + 1 ≤ k := Nat.succ_le_of_lt this
            exact ⟨k, this, hk.2.1, hk.2.2⟩
        · exact Nat.lt_of_not_ge h1

-- LLM HELPER
lemma has_divisor_in_range_false (n start stop: Nat) :
  has_divisor_in_range n start stop = false ↔ 
  ¬ ∃ k, start ≤ k ∧ k < stop ∧ n % k = 0 := by
  constructor
  · intro h
    intro ⟨k, hk⟩
    have : has_divisor_in_range n start stop = true := by
      rw [has_divisor_in_range_spec]
      exact ⟨k, hk⟩
    rw [h] at this
    exact Bool.false_ne_true this
  · intro h
    by_cases h_case : has_divisor_in_range n start stop = true
    · rw [has_divisor_in_range_spec] at h_case
      exact False.elim (h h_case)
    · simp at h_case
      exact h_case

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use (if n < 2 then false else ¬ has_divisor_in_range n 2 n)
  constructor
  · rfl
  · simp
    by_cases h : n < 2
    · simp [h]
      constructor
      · intro h_false
        intro ⟨k, hk⟩
        have : k ≥ 2 := hk.1
        have : k < n := hk.2.1
        have : n ≥ 2 := Nat.le_trans hk.1 (Nat.le_of_lt hk.2.1)
        exact Nat.not_lt.mpr this h
      · intro _
        rfl
    · simp [h]
      rw [has_divisor_in_range_false]
      rfl