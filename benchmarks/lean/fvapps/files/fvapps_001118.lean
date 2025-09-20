-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_helper_thanks (n : Int) : String :=
sorry

def solve_multiple_cases (nums : List Int) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_helper_thanks_result_valid (n : Int) :
  (solve_helper_thanks n = "-1") ∨
  (solve_helper_thanks n = "Thanks for helping Chef!") :=
sorry

theorem solve_multiple_cases_length (nums : List Int) :
  (solve_multiple_cases nums).length = nums.length :=
sorry

theorem solve_helper_thanks_condition (n : Int) :
  (n < 10) = (solve_helper_thanks n = "Thanks for helping Chef!") :=
sorry

theorem solve_multiple_cases_valid_results (nums : List Int) :
  ∀ x ∈ solve_multiple_cases nums,
    (x = "-1") ∨ (x = "Thanks for helping Chef!") :=
sorry

theorem solve_multiple_cases_condition (nums : List Int) :
  ∀ (i : Nat), i < nums.length →
    ((nums[i]! < 10) =
     ((solve_multiple_cases nums)[i]! = "Thanks for helping Chef!")) :=
sorry
-- </vc-theorems>