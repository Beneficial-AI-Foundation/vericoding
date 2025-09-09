-- <vc-helpers>
-- </vc-helpers>

def xorOperation (n: Nat) (start: Nat) : Nat :=
  sorry

theorem xorOperation_non_negative (n: Nat) (start: Nat) : 
  xorOperation n start ≥ 0 := 
  sorry

theorem xorOperation_zero (start: Nat) :
  xorOperation 0 start = 0 :=
  sorry

theorem xorOperation_one (start: Nat) :
  xorOperation 1 start = start :=
  sorry

theorem xorOperation_deterministic (n: Nat) (start: Nat) :
  xorOperation n start = xorOperation n start :=
  sorry

theorem xorOperation_edge_case_zero :
  xorOperation 0 100 = 0 :=
  sorry

theorem xorOperation_edge_case_one :
  xorOperation 1 5 = 5 :=
  sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval xor_operation 5 0

/-
info: 8
-/
-- #guard_msgs in
-- #eval xor_operation 4 3

/-
info: 7
-/
-- #guard_msgs in
-- #eval xor_operation 1 7

-- Apps difficulty: introductory
-- Assurance level: guarded