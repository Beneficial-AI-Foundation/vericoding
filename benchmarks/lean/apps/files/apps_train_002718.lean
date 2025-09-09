-- <vc-helpers>
-- </vc-helpers>

def gap (n : Nat) : Nat := sorry

theorem gap_bounded (n : Nat) (h : n > 0):
  gap n ≤ n.log2 :=
sorry

theorem no_gaps_all_ones (n : Nat):
  gap ((1 <<< n) - 1) = 0 :=
sorry

theorem leading_trailing_zeros (n k : Nat) (h : n > 0):
  gap n = gap (n <<< k) :=
sorry

theorem single_bit_no_gap (n : Nat):
  gap (1 <<< n) = 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval gap 9

/-
info: 4
-/
-- #guard_msgs in
-- #eval gap 529

/-
info: 0
-/
-- #guard_msgs in
-- #eval gap 15

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible