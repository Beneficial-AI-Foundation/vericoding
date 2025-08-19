def problem_spec
-- function signature
(impl: Nat → Nat → Nat → Bool)
-- inputs
(a b c: Nat) :=
-- spec
let spec (result: Bool) :=
result ↔
  0 < a ∧ 0 < b ∧ 0 < c ∧
  ((a * a + b * b = c * c) ∨
  (a * a + c * c = b * b) ∨
  (b * b + c * c = a * a))
-- program terminates
∃ result, impl a b c = result ∧
-- return value satisfies spec
spec result

def implementation (a b c: Nat) : Bool := 
  decide (0 < a) && decide (0 < b) && decide (0 < c) &&
  (decide (a * a + b * b = c * c) ||
   decide (a * a + c * c = b * b) ||
   decide (b * b + c * c = a * a))

-- LLM HELPER
lemma bool_and_or_simp (p q r s t u : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] [Decidable t] [Decidable u] : 
  (decide p && decide q && decide r && (decide s || decide t || decide u)) = true ↔ 
  p ∧ q ∧ r ∧ (s ∨ t ∨ u) := by
  simp [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true]

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  simp [problem_spec, implementation]
  use (decide (0 < a) && decide (0 < b) && decide (0 < c) &&
      (decide (a * a + b * b = c * c) ||
       decide (a * a + c * c = b * b) ||
       decide (b * b + c * c = a * a)))
  constructor
  · rfl
  · apply bool_and_or_simp