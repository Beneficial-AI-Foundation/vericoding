-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def atomic_number (n: Nat) : List Nat := sorry

theorem atomic_number_sum_equals_input (n: Nat) :
  n > 0 → (atomic_number n).foldr (· + ·) 0 = n := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem atomic_number_shell_capacity (n: Nat) (i: Nat) :
  n > 0 → i > 0 → i ≤ (atomic_number n).length → 
  (atomic_number n).get ⟨i-1, sorry⟩ ≤ 2 * i * i := by sorry 

theorem atomic_number_shells_filled_in_order (n: Nat) (i: Nat) :
  n > 0 → i + 1 < (atomic_number n).length →
  (atomic_number n).get ⟨i, sorry⟩ = 2 * (i + 1) * (i + 1) := by sorry
-- </vc-theorems>