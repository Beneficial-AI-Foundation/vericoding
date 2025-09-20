-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_divisible (n x y : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_divisible_implies_individual_divisibility 
  {n x y : Int} (h : x ≠ 0) (h' : y ≠ 0) :
  is_divisible n x y → n % x = 0 ∧ n % y = 0 :=
  sorry

theorem divisible_by_x_implies_divisible_with_one 
  {n x : Int} (h : x ≠ 0) :
  n % x = 0 → is_divisible n x 1 ∧ is_divisible n 1 x :=
  sorry

theorem non_zero_divisible_by_self 
  {n : Int} (h : n ≠ 0) :
  is_divisible n n 1 ∧ is_divisible n 1 n :=
  sorry
-- </vc-theorems>