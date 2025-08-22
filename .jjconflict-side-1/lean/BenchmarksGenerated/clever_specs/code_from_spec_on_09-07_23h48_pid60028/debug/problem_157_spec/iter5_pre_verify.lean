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
  0 < a && 0 < b && 0 < c &&
  ((a * a + b * b == c * c) ||
   (a * a + c * c == b * b) ||
   (b * b + c * c == a * a))

-- LLM HELPER
lemma pos_and_pyth_equiv (a b c: Nat) : 
  (0 < a && 0 < b && 0 < c &&
   ((a * a + b * b == c * c) ||
    (a * a + c * c == b * b) ||
    (b * b + c * c == a * a))) = true ↔
  (0 < a ∧ 0 < b ∧ 0 < c ∧
   ((a * a + b * b = c * c) ∨
    (a * a + c * c = b * b) ∨
    (b * b + c * c = a * a))) := by
  simp [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

-- LLM HELPER
lemma not_pos_or_not_pyth_equiv (a b c: Nat) :
  (0 < a && 0 < b && 0 < c &&
   ((a * a + b * b == c * c) ||
    (a * a + c * c == b * b) ||
    (b * b + c * c == a * a))) = false ↔
  ¬(0 < a ∧ 0 < b ∧ 0 < c ∧
    ((a * a + b * b = c * c) ∨
     (a * a + c * c = b * b) ∨
     (b * b + c * c = a * a))) := by
  simp [Bool.and_eq_false_iff, Bool.or_eq_false_iff, beq_iff_eq]
  constructor
  · intro h
    cases h with
    | inl h1 => 
      simp [h1]
    | inr h2 => 
      cases h2 with
      | inl h21 => 
        simp [h21]
      | inr h22 => 
        cases h22 with
        | inl h221 => 
          simp [h221]
        | inr h222 => 
          simp [h222]
  · intro h
    simp at h
    cases h with
    | inl h1 => 
      left
      exact h1
    | inr h2 => 
      cases h2 with
      | inl h21 => 
        right
        left
        exact h21
      | inr h22 => 
        cases h22 with
        | inl h221 => 
          right
          right
          left
          exact h221
        | inr h222 => 
          right
          right
          right
          exact h222

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec implementation
  simp
  use (0 < a && 0 < b && 0 < c &&
       ((a * a + b * b == c * c) ||
        (a * a + c * c == b * b) ||
        (b * b + c * c == a * a)))
  constructor
  · rfl
  · cases h : (0 < a && 0 < b && 0 < c &&
               ((a * a + b * b == c * c) ||
                (a * a + c * c == b * b) ||
                (b * b + c * c == a * a)))
    · simp [h]
      exact (not_pos_or_not_pyth_equiv a b c).mp h
    · simp [h]
      exact (pos_and_pyth_equiv a b c).mp h