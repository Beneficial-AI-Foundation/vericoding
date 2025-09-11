-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_remainder_parity (N M : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_remainder_parity_returns_valid_string 
  (N : Int) (M : Int) (h : M ≠ 0) :
  check_remainder_parity N M = "ODD" ∨ 
  check_remainder_parity N M = "EVEN" :=
sorry

theorem check_remainder_parity_matches_modulo
  (N : Int) (M : Int) (h : M ≠ 0) :
  (check_remainder_parity N M = "EVEN" ∧ N % M % 2 = 0) ∨ 
  (check_remainder_parity N M = "ODD" ∧ N % M % 2 = 1) :=
sorry

theorem check_remainder_parity_consistent
  (N : Int) (M : Int) (h : M ≠ 0) :
  check_remainder_parity N M = check_remainder_parity N M :=
sorry

/-
info: 'EVEN'
-/
-- #guard_msgs in
-- #eval check_remainder_parity 4 4

/-
info: 'ODD'
-/
-- #guard_msgs in
-- #eval check_remainder_parity 6 5

/-
info: 'ODD'
-/
-- #guard_msgs in
-- #eval check_remainder_parity 10 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded