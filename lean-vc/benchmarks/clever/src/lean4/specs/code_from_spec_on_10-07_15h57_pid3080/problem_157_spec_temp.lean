import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
  (a * a + b * b == c * c || 
   a * a + c * c == b * b || 
   b * b + c * c == a * a)

-- LLM HELPER
lemma bool_and_iff (p q : Bool) : (p && q) = true ↔ p = true ∧ q = true := by
  cases p <;> cases q <;> simp

-- LLM HELPER
lemma bool_or_iff (p q r : Bool) : (p || q || r) = true ↔ p = true ∨ q = true ∨ r = true := by
  cases p <;> cases q <;> cases r <;> simp

-- LLM HELPER
lemma nat_beq_iff (m n : Nat) : (m == n) = true ↔ m = n := by
  cases Nat.decEq m n with
  | isTrue h => simp [h, Nat.beq_refl]
  | isFalse h => simp [Nat.beq_false_of_ne h, h]

-- LLM HELPER
lemma nat_pos_iff (n : Nat) : (0 < n) = true ↔ 0 < n := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.zero_lt_succ]

theorem correctness
(a b c: Nat)
: problem_spec implementation a b c := by
  unfold problem_spec
  use (0 < a && 0 < b && 0 < c && 
       (a * a + b * b == c * c || 
        a * a + c * c == b * b || 
        b * b + c * c == a * a))
  constructor
  · rfl
  · unfold implementation
    simp only [Bool.decide_eq_true]
    constructor
    · intro h
      rw [bool_and_iff] at h
      cases' h with h_pos h_pyth
      rw [bool_and_iff] at h_pos
      cases' h_pos with h_a h_bc
      rw [bool_and_iff] at h_bc
      cases' h_bc with h_b h_c
      rw [bool_or_iff] at h_pyth
      cases' h_pyth with h1 h_rest
      · exact ⟨h_a, h_b, h_c, Or.inl (nat_beq_iff _ _ |>.mp h1)⟩
      · cases' h_rest with h2 h3
        · exact ⟨h_a, h_b, h_c, Or.inr (Or.inl (nat_beq_iff _ _ |>.mp h2))⟩
        · exact ⟨h_a, h_b, h_c, Or.inr (Or.inr (nat_beq_iff _ _ |>.mp h3))⟩
    · intro h
      cases' h with h_a h_rest
      cases' h_rest with h_b h_rest
      cases' h_rest with h_c h_pyth
      rw [bool_and_iff, bool_and_iff, bool_and_iff, bool_or_iff]
      constructor
      · exact ⟨h_a, h_b, h_c⟩
      · cases' h_pyth with h1 h_rest
        · exact Or.inl (nat_beq_iff _ _ |>.mpr h1)
        · cases' h_rest with h2 h3
          · exact Or.inr (Or.inl (nat_beq_iff _ _ |>.mpr h2))
          · exact Or.inr (Or.inr (nat_beq_iff _ _ |>.mpr h3))