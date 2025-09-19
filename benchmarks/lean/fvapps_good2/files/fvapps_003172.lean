-- <vc-preamble>
def sum_list : List Int → Int
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ones_counter (nums : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ones_counter_positive (nums : List Int) :
  ∀ x ∈ ones_counter nums, x > 0
:=
sorry

theorem ones_counter_sum (nums : List Int) :
  sum_list (ones_counter nums) = sum_list nums
:=
sorry

theorem ones_counter_grouped (nums : List Int) :
  ones_counter nums =
    let rec group_ones (ns : List Int) (acc : Int) (result : List Int) : List Int :=
      match ns with
      | [] => if acc > 0 then result ++ [acc] else result
      | x::xs => if x = 1
                 then group_ones xs (acc + 1) result
                 else if acc > 0
                      then group_ones xs 0 (result ++ [acc])
                      else group_ones xs 0 result
    group_ones nums 0 []
:=
sorry

theorem ones_counter_all_zeros {nums : List Int} (h : ∀ x ∈ nums, x = 0) :
  ones_counter nums = []
:=
sorry

theorem ones_counter_all_ones {nums : List Int} (h : ∀ x ∈ nums, x = 1) (h' : nums ≠ []) :
  ones_counter nums = [((List.length nums) : Int)]
:=
sorry
-- </vc-theorems>