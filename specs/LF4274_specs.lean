-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vampire_number (n: Nat): Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vampire_number_gives_positive {n: Nat} (h: 1 ≤ n ∧ n ≤ 155): 
  vampire_number n > 0 := 
  sorry

theorem vampire_result_has_even_digits {n: Nat} (h: 1 ≤ n ∧ n ≤ 155):
  ∃ k, String.length (Nat.repr (vampire_number n)) = 2 * k :=
  sorry

theorem vampire_has_valid_factors {n: Nat} (h: 1 ≤ n ∧ n ≤ 155): 
  ∃ x y: Nat, 
    -- x and y are factors
    vampire_number n = x * y ∧ 
    -- x and y have equal number of digits
    String.length (Nat.repr x) = String.length (Nat.repr y) ∧
    -- Combined digits of factors give original number
    Nat.repr x ++ Nat.repr y = Nat.repr (vampire_number n) ∧
    -- Not both ending in 0
    ¬(x % 10 = 0 ∧ y % 10 = 0) :=
  sorry

theorem vampire_numbers_increasing {n₁ n₂: Nat} 
  (h₁: 1 ≤ n₁ ∧ n₁ ≤ 155) (h₂: 1 ≤ n₂ ∧ n₂ ≤ 155) (h₃: n₁ < n₂):
  vampire_number n₁ < vampire_number n₂ :=
  sorry

theorem vampire_undefined_outside_range (n: Nat) (h: n ≥ 156):
  ¬∃ m: Nat, vampire_number n = m :=
  sorry
-- </vc-theorems>