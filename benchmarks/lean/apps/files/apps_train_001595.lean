-- <vc-helpers>
-- </vc-helpers>

def solve_runes (s : String) : Int := sorry

theorem solve_runes_addition {a b : Nat}
  (h1 : a ≤ 100) (h2 : b ≤ 100) :
  let expr := s!"?+?={a + b}"
  let result := solve_runes expr
  result ≠ -1 → result = a ∧ result = b := sorry

theorem solve_runes_subtraction {a b : Nat}
  (h1 : a ≤ 100) (h2 : b ≤ 100) :
  let expr := s!"?-?={a - b}"
  let result := solve_runes expr 
  result ≠ -1 → result = a ∧ result = b := sorry

theorem solve_runes_no_leading_zeros {d : Nat}
  (h : d ≤ 9) :
  solve_runes s!"0?=0{d}" = -1 := sorry

theorem basic_addition :
  solve_runes "1+1=?" = 2 := sorry

theorem basic_addition_unknown :
  solve_runes "?+?=2" = 1 := sorry

theorem basic_negative :
  solve_runes "-?=-?" = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_runes "123?45*?=?"

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_runes "??+??=??"

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_runes "-?56373--9216=-?47157"

-- Apps difficulty: interview
-- Assurance level: unguarded