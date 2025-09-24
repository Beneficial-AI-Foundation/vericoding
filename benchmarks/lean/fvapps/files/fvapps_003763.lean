-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powerof4 {α : Type} (x : α) : Bool := sorry

theorem powerof4_positive_integers (n : Nat) :
  n ≥ 1 ∧ n ≤ 1000000 →
  powerof4 n = true ↔ (n = 1 ∨ (∃ k : Nat, n = 4 * 4^k)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem powerof4_float_property (n : Float) :
  n > 0 ∧ n ≤ 1000000 →
  powerof4 n = true → 
  ∃ k : Nat, n = Float.ofNat (4 * 4^k) := sorry

theorem powerof4_string_false (s : String) :
  powerof4 s = false := sorry

theorem powerof4_nonpositive_false (n : Int) :
  n ≤ 0 → powerof4 n = false := sorry

theorem powerof4_other_types_false (x : Unit ⊕ List Nat ⊕ Array Nat) :
  powerof4 x = false := sorry
-- </vc-theorems>