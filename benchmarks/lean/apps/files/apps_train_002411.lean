-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getSum (a b : Int) : Int := sorry

theorem getSum_with_zero (a : Int) : 
  getSum a 0 = a ∧ getSum 0 a = a := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem getSum_commutative (a b : Int) :
  getSum a b = getSum b a := sorry

theorem getSum_associative (a b c : Int) :
  getSum (getSum a b) c = getSum a (getSum b c) := sorry

theorem getSum_negation (a : Int) :
  getSum a (-a) = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval getSum 1 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval getSum 5 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval getSum -2 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded