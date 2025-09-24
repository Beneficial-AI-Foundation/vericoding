-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_layer_sum (n : Nat) (layers : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_layer_sum_single_digit_pos (n : Nat) (h : n > 0) :
  calc_layer_sum n (List.replicate n 1) > 0 :=
  sorry

theorem calc_layer_sum_zero_is_zero : 
  calc_layer_sum 1 [0] = 0 :=
  sorry

theorem calc_layer_sum_one_is_one :
  calc_layer_sum 1 [1] = 1 :=
  sorry

theorem calc_layer_sum_same_digits (d : Nat) :
  calc_layer_sum 2 [d, d] = calc_layer_sum 2 [d, d] :=
  sorry

theorem calc_layer_sum_order_indep :
  calc_layer_sum 2 [1, 2] = calc_layer_sum 2 [2, 1] :=
  sorry
-- </vc-theorems>