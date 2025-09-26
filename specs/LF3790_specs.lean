-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alternate_sq_sum (l : List Int) : Int := sorry

theorem alternate_sq_sum_empty :
  alternate_sq_sum [] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alternate_sq_sum_formula (l : List Int) :
  alternate_sq_sum l = (List.enum l).foldr (fun (i, x) acc => 
    acc + if i % 2 = 1 then x * x else x) 0 := sorry

theorem alternate_sq_sum_singleton (x : Int) :
  alternate_sq_sum [x] = x := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval alternate_sq_sum []

/-
info: 0
-/
-- #guard_msgs in
-- #eval alternate_sq_sum [-1, 0, -3, 0, -5, 3]

/-
info: 379
-/
-- #guard_msgs in
-- #eval alternate_sq_sum [11, 12, 13, 14, 15]
-- </vc-theorems>