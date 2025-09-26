-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_max_number (numbers : List Nat) :
  let s := numbers.foldr (fun n acc => s!"a{n}b" ++ acc) ""
  solve s = numbers.maximum?.getD 0
  := by sorry

theorem solve_returns_nat (s : String) :
  0 ≤ solve s
  := by sorry

theorem solve_is_max_in_string (s : String) :
  let digits := s.toList.filter Char.isDigit
  let numbers := digits.map (λ c => c.toNat - '0'.toNat)
  solve s = numbers.maximum?.getD 0
  := by sorry

/-
info: 695
-/
-- #guard_msgs in
-- #eval solve "gh12cdy695m1"

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve "2ti9iei7qhr5"

/-
info: 61
-/
-- #guard_msgs in
-- #eval solve "vih61w8oohj5"
-- </vc-theorems>