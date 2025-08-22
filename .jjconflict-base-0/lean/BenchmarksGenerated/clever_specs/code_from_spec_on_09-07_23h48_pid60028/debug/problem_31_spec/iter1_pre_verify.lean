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
  sorry

-- LLM HELPER
lemma has_divisor_in_range_false (n start stop: Nat) :
  has_divisor_in_range n start stop = false ↔ 
  ¬ ∃ k, start ≤ k ∧ k < stop ∧ n % k = 0 := by
  sorry

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
        have : n > k := this
        have : n ≥ 2 := Nat.le_trans this.1 this
        have : n ≥ 2 := Nat.le_trans hk.1 (Nat.le_of_lt hk.2.1)
        exact Nat.not_lt.mpr this h
      · intro _
        rfl
    · simp [h]
      rw [has_divisor_in_range_false]
      constructor
      · intro h_no_div
        exact h_no_div
      · intro h_no_div
        exact h_no_div