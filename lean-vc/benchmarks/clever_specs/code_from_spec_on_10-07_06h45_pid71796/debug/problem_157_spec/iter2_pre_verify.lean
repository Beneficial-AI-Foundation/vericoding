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
lemma bool_and_iff (p q : Prop) [Decidable p] [Decidable q] : 
  (decide p && decide q) = true ↔ p ∧ q := by
  simp [Bool.and_eq_true, decide_eq_true]

-- LLM HELPER
lemma bool_or_iff (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] : 
  (decide p || decide q || decide r) = true ↔ p ∨ q ∨ r := by
  simp [Bool.or_eq_true, decide_eq_true]

-- LLM HELPER  
lemma nat_eq_decidable (a b : Nat) : Decidable (a = b) := by
  infer_instance

-- LLM HELPER
lemma nat_lt_decidable (a b : Nat) : Decidable (a < b) := by
  infer_instance

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
  · simp [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true]
    constructor
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩