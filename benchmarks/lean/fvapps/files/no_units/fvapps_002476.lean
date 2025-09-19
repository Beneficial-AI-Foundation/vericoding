-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_sum_product : List (List Int) → Int
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_sum_product_2x2_matrix {a b c d : Int} :
  array_sum_product [[a, b], [c, d]] = (a + c) * (b + d) :=
sorry

theorem array_sum_product_all_ones {rows cols : Nat} (h₁ : rows > 0) (h₂ : cols > 0) :
  let matrix := List.replicate rows (List.replicate cols 1)
  array_sum_product matrix = rows ^ cols :=
sorry
-- </vc-theorems>