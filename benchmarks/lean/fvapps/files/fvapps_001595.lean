-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_runes (s : String) : Int := sorry

theorem solve_runes_addition {a b : Nat}
  (h1 : a ≤ 100) (h2 : b ≤ 100) :
  let expr := s!"?+?={a + b}"
  let result := solve_runes expr
  result ≠ -1 → result = a ∧ result = b := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>