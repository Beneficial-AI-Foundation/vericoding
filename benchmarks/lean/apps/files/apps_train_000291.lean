-- <vc-helpers>
-- </vc-helpers>

def multiply (a b : String) : String := sorry 

theorem multiply_matches_integer_multiplication {a b : Nat} : 
  multiply (toString a) (toString b) = toString (a * b) := sorry

theorem multiply_by_zero {n : String} : 
  (multiply n "0" = "0") ∧ (multiply "0" n = "0") := sorry

theorem multiply_by_one {n : String} :
  (multiply n "1" = n) ∧ (multiply "1" n = n) := sorry

theorem multiply_commutative {a b : String} :
  multiply a b = multiply b a := sorry

theorem multiply_associative {a b c : String} :
  multiply (multiply a b) c = multiply a (multiply b c) := sorry

/-
info: '6'
-/
-- #guard_msgs in
-- #eval multiply "2" "3"

/-
info: '56088'
-/
-- #guard_msgs in
-- #eval multiply "123" "456"

/-
info: '0'
-/
-- #guard_msgs in
-- #eval multiply "0" "0"

-- Apps difficulty: interview
-- Assurance level: unguarded