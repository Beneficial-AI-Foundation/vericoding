-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_scholarships (n r p q : Nat) (x_arr y_arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_arrays_result_bounded
    (n r : Nat) (h1 : 0 < n) (h2 : n ≤ 1000) (h3 : r ≤ 1000) :
    let result := calc_scholarships n r 0 0 [] []
    0 ≤ result ∧ result ≤ n ∧ result ≤ r ∧ result = min n r :=
  sorry

theorem full_ineligible_is_zero
    (n r : Nat) (h1 : 0 < n) (h2 : n ≤ 100) (h3 : r ≤ 100) :
    let x_arr := List.range n
    calc_scholarships n r n 0 x_arr [] = 0 :=
  sorry
-- </vc-theorems>