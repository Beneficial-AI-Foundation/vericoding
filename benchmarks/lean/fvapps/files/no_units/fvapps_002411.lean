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
-- </vc-theorems>