-- <vc-helpers>
-- </vc-helpers>

def array_sum_product : List (List Int) → Int
  | _ => sorry

theorem array_sum_product_2x2_matrix {a b c d : Int} :
  array_sum_product [[a, b], [c, d]] = (a + c) * (b + d) :=
sorry

theorem array_sum_product_all_ones {rows cols : Nat} (h₁ : rows > 0) (h₂ : cols > 0) :
  let matrix := List.replicate rows (List.replicate cols 1)
  array_sum_product matrix = rows ^ cols :=
sorry

/-
info: 24
-/
-- #guard_msgs in
-- #eval array_sum_product [[1, 2], [3, 4]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval array_sum_product [[1, 1], [1, 1]]

/-
info: 15
-/
-- #guard_msgs in
-- #eval array_sum_product [[1, 2], [2, 3]]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible