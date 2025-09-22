-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves (nums : List Int) : Int :=
sorry

def list_minimum (nums : List Int) : Int :=
sorry

def list_maximum (nums : List Int) : Int :=
sorry

def list_sum (nums : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_moves_non_negative (nums : List Int) (h : nums ≠ []) :
  min_moves nums ≥ 0 :=
sorry

theorem min_moves_equal_elements (n : Int) (len : Nat) (h : len ≥ 1) :
  min_moves (List.replicate len n) = 0 :=
sorry

theorem min_moves_upper_bound (nums : List Int) (h : nums ≠ []) :
  let min_val := list_minimum nums
  min_moves nums ≤ list_sum (nums.map (λ x => x - min_val)) :=
sorry

theorem min_moves_monotonic (nums : List Int) (h : nums.length ≥ 2) :
  let new_nums := nums ++ [list_maximum nums]
  min_moves new_nums ≥ min_moves nums :=
sorry
-- </vc-theorems>