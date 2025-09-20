-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_make_proportion (a b c d : Int) : String := sorry 

/- If a:b = c:d where c=2a and d=2b, then a proportion is possible -/
-- </vc-definitions>

-- <vc-theorems>
theorem proportional_numbers_are_possible {a b : Int} (ha : a > 0) (hb : b > 0) :
  can_make_proportion a b (2*a) (2*b) = "Possible" := sorry

/- The result is invariant under reordering the ratios -/

theorem order_invariant {a b c d : Int} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
  can_make_proportion a b c d = can_make_proportion b a d c ∧ 
  can_make_proportion a b c d = can_make_proportion c d a b := sorry

/- Same number always forms valid proportion -/

theorem same_number_possible {n : Int} (hn : n > 0) :
  can_make_proportion n n n n = "Possible" := sorry

/- Zero numerator with non-zero denominator is possible, but zero denominator raises error -/

theorem zero_division {n : Int} (hn : n > 0) :
  can_make_proportion 0 n 0 (2*n) = "Possible" := sorry
-- </vc-theorems>