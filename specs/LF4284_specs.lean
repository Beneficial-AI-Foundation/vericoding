-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_number (n : Nat) : Nat := sorry

theorem max_number_type (n : Nat) : Nat.succ (max_number n) > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_number_digit_count (n : Nat) : 
  String.length (toString (max_number n)) = String.length (toString n) := sorry

theorem max_number_same_digits (n : Nat) :
  (toString (max_number n)).data = (toString n).data := sorry

theorem max_number_geq_input (n : Nat) : 
  max_number n ≥ n := sorry

theorem max_number_digits_descending (n : Nat) (i : String.Pos) : 
  i.1 + 1 < String.length (toString (max_number n)) →
  (toString (max_number n)).get i ≥ (toString (max_number n)).get ⟨i.1 + 1⟩ := sorry

theorem max_number_idempotent (n : Nat) :
  max_number (max_number n) = max_number n := sorry

theorem max_number_deterministic (n : Nat) :
  max_number n = max_number n := sorry
-- </vc-theorems>