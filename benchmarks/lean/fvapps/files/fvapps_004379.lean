-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_2d_list (head : Int) (row : Nat) (col : Nat) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem make_2d_list_dimensions {head : Int} {row col : Nat} 
  (h1 : row > 0) (h2 : col > 0) :
  let result := make_2d_list head row col
  result.length = row ∧ 
  ∀ r ∈ result, r.length = col :=
sorry

theorem make_2d_list_row_increment {head : Int} {row col : Nat}
  (h1 : row > 0) (h2 : col > 0) :
  let result := make_2d_list head row col
  ∀ r ∈ result, ∀ i, i + 1 < r.length → 
    (r.get! (i+1)) - (r.get! i) = 1 :=
sorry

theorem make_2d_list_col_increment {head : Int} {row col : Nat}  
  (h1 : row > 0) (h2 : col > 0) :
  let result := make_2d_list head row col
  ∀ i j, i + 1 < result.length → j < col → 
    (result.get! (i+1)).get! j - (result.get! i).get! j = col :=
sorry

theorem make_2d_list_head {head : Int} {row col : Nat}
  (h1 : row > 0) (h2 : col > 0) :
  let result := make_2d_list head row col
  (result.get! 0).get! 0 = head :=
sorry

theorem make_2d_list_square {head : Int} {size : Nat}
  (h : size > 0) :
  let result := make_2d_list head size size
  result.length = (result.get! 0).length :=
sorry
-- </vc-theorems>