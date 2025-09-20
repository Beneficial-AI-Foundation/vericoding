-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_pal (n : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_pal_returns_valid_list (n : Nat) (h : n > 0 ∧ n ≤ 5) :
  let result := count_pal n
  List.length result = 2 ∧
  ∀ x ∈ result, x ≥ 0 ∧
  List.get! result 1 ≥ List.get! result 0 :=
sorry

theorem count_pal_edge_case_single_digit :
  (count_pal 1).get! 0 = 9 ∧
  let total := (count_pal 1).get! 1
  total > 0 ∧ total < 10 :=
sorry

theorem count_pal_monotonic (n : Nat) (h : n > 0 ∧ n ≤ 4) :
  (count_pal n).get! 1 ≤ (count_pal (n+1)).get! 1 :=
sorry
-- </vc-theorems>