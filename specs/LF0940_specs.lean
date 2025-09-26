-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Activity := String × Nat

def calculate_max_months (input : List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiple_test_cases_properties
  (n : Nat)
  (h : n > 0 ∧ n ≤ 5) :
  let result := calculate_max_months ([toString n] ++ 
    (List.range n).bind (fun i => 
      [s!"1 {if i % 2 = 0 then "INDIAN" else "NON_INDIAN"}", 
       "BUG_FOUND 1000"]))
  result.length = n ∧
  (∀ i, i < n → result[i]! > 0) ∧
  (∀ i, 0 < i → i < n → i % 2 = 1 → result[i]! ≤ result[i-1]!) :=
sorry

theorem contest_won_rank_bonus
  (rank : Nat)
  (h : rank > 0 ∧ rank ≤ 20) :
  let result := calculate_max_months ["1", "2 INDIAN", s!"CONTEST_WON {rank}", "CONTEST_WON 21"]
  let worse_result := calculate_max_months ["1", "2 INDIAN", "CONTEST_WON 21", "CONTEST_WON 21"]
  result[0]! ≥ worse_result[0]! :=
sorry

/-
info: [3, 1]
-/
-- #guard_msgs in
-- #eval calculate_max_months ["2", "4 INDIAN", "CONTEST_WON 1", "TOP_CONTRIBUTOR", "BUG_FOUND 100", "CONTEST_HOSTED", "4 NON_INDIAN", "CONTEST_WON 1", "TOP_CONTRIBUTOR", "BUG_FOUND 100", "CONTEST_HOSTED"]

/-
info: [3]
-/
-- #guard_msgs in
-- #eval calculate_max_months ["1", "2 INDIAN", "CONTEST_WON 5", "TOP_CONTRIBUTOR"]

/-
info: [2]
-/
-- #guard_msgs in
-- #eval calculate_max_months ["1", "1 NON_INDIAN", "BUG_FOUND 1000"]
-- </vc-theorems>