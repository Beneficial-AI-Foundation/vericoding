-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def triangle_type (a b c : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangle_type_symmetric (a b c : Int) : 
  a > 0 → b > 0 → c > 0 →
  triangle_type a b c = triangle_type a c b ∧
  triangle_type a b c = triangle_type b a c ∧ 
  triangle_type a b c = triangle_type b c a ∧
  triangle_type a b c = triangle_type c a b ∧
  triangle_type a b c = triangle_type c b a :=
sorry

theorem triangle_inequality (a b c : Int) :
  a > 0 → b > 0 → c > 0 →
  let x := min a (min b c)
  let y := max (min a (max b c)) (min b c)
  let z := max a (max b c) 
  (if z ≥ x + y then triangle_type a b c = 0 
   else triangle_type a b c ≠ 0) :=
sorry

theorem right_triangle_scaling (a b c : Int) :
  a > 0 → b > 0 → 
  c*c = a*a + b*b →
  triangle_type a b c = 2 ∧
  triangle_type (2*a) (2*b) (2*c) = 2 :=
sorry

theorem triangle_type_range (a b c : Int) :
  a > 0 → b > 0 → c > 0 →
  triangle_type a b c = 0 ∨ 
  triangle_type a b c = 1 ∨
  triangle_type a b c = 2 ∨ 
  triangle_type a b c = 3 :=
sorry
-- </vc-theorems>