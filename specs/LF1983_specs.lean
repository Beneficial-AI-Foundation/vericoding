-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_magnets (n : Nat) (k : Nat) (magnets : List Magnet) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem basic_case_theorem :
  let n := 3
  let k := 1
  let magnets := [
    Magnet.mk 1 1 2 2,
    Magnet.mk 2 2 3 3,
    Magnet.mk 3 3 4 4
  ]
  solve_magnets n k magnets = 1 :=
sorry

theorem zero_k_theorem :
  let n := 2
  let k := 0
  let magnets := [
    Magnet.mk 1 1 2 2,
    Magnet.mk 3 3 4 4
  ]
  solve_magnets n k magnets > 0 :=
sorry

theorem large_gap_theorem :
  let n := 2
  let k := 1
  let magnets := [
    Magnet.mk 1 1 2 2,
    Magnet.mk 100 100 101 101
  ]
  solve_magnets n k magnets = 1 :=
sorry

theorem given_case_theorem :
  let n := 4
  let k := 1
  let magnets := [
    Magnet.mk 1 1 2 2,
    Magnet.mk 1 9 2 10,
    Magnet.mk 9 9 10 10,
    Magnet.mk 9 1 10 2
  ]
  solve_magnets n k magnets = 64 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_magnets 3 1 [(1, 1, 2, 2), (2, 2, 3, 3), (3, 3, 4, 4)]

/-
info: 64
-/
-- #guard_msgs in
-- #eval solve_magnets 4 1 [(1, 1, 2, 2), (1, 9, 2, 10), (9, 9, 10, 10), (9, 1, 10, 2)]

/-
info: 249999999000000001
-/
-- #guard_msgs in
-- #eval solve_magnets 3 0 [(1, 1, 2, 2), (1, 1, 1000000000, 1000000000), (1, 3, 8, 12)]
-- </vc-theorems>