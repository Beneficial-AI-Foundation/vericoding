-- <vc-helpers>
-- </vc-helpers>

def derive (coefficient : Int) (exponent : Int) : String := sorry 

theorem derive_coefficient_correct {c e : Int} 
  (h : e > 0) : 
  let result := derive c e
  let coef := result.splitOn "x^" |>.get! 0
  String.toInt! coef = c * e := sorry

theorem derive_exponent_correct {c e : Int}
  (h : e > 0) :
  let result := derive c e
  let exp := result.splitOn "x^" |>.get! 1 
  String.toInt! exp = e - 1 := sorry

theorem derive_format {c e : Int}
  (h : e > 0) :
  String.contains (derive c e) 'x' := sorry

theorem derive_matches_derivative_formula {c e : Int}
  (h : e > 0) :
  derive c e = toString (c * e) ++ "x^" ++ toString (e - 1) := sorry

/-
info: '56x^7'
-/
-- #guard_msgs in
-- #eval derive 7 8

/-
info: '45x^8'
-/
-- #guard_msgs in
-- #eval derive 5 9

/-
info: '20x^1'
-/
-- #guard_msgs in
-- #eval derive 10 2

-- Apps difficulty: introductory
-- Assurance level: unguarded