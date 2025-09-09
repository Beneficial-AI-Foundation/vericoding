-- <vc-helpers>
-- </vc-helpers>

def solve_weighted_sum (numbers : List Int) : Int × Float := sorry

theorem no_great_numbers {nums : List Int} (h : ∀ n ∈ nums, n ≤ 30) :
  (solve_weighted_sum (nums ++ [-1])).1 = 0 := sorry

theorem all_great_numbers {nums : List Int} (h : ∀ n ∈ nums, n > 30) :
  (solve_weighted_sum (nums ++ [-1])).1 = nums.length := sorry

theorem average_bounds {nums : List Int} (h : ∀ n ∈ nums, n ≥ 0) : 
  let avg := (solve_weighted_sum (nums ++ [-1])).2
  avg = 0 ∨ avg ≥ 0 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded