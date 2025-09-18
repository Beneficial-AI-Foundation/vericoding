-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compress_image (m n : Nat) (grid : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compress_minimal_cases_2x2_perfect (grid : List String) :
  grid = ["11", "11"] → compress_image 2 2 grid = 0 :=
sorry

theorem compress_minimal_cases_2x2_worst (grid : List String) :
  grid = ["10", "01"] → compress_image 2 2 grid = 2 :=
sorry

theorem compress_minimal_cases_rect_2x3 (grid : List String) :
  grid = ["010", "101"] → compress_image 2 3 grid = 3 :=
sorry

theorem compress_minimal_cases_rect_3x2 (grid : List String) :
  grid = ["01", "10", "01"] → compress_image 3 2 grid = 3 :=
sorry

theorem compress_example_case (grid : List String) :
  grid = ["00100", "10110", "11001"] → compress_image 3 5 grid = 5 :=
sorry

theorem compress_larger_3x3_all_ones (grid : List String) :
  grid = ["111", "111", "111"] → compress_image 3 3 grid = 0 :=
sorry

theorem compress_larger_3x3_all_zeros (grid : List String) :
  grid = ["000", "000", "000"] → compress_image 3 3 grid = 0 :=
sorry

theorem compress_larger_3x3_checkerboard (grid : List String) :
  grid = ["101", "010", "101"] → compress_image 3 3 grid = 4 :=
sorry
-- </vc-theorems>