-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_reachable (t: String) (queries: List (Nat × Nat × Nat)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_reachable_results_match_queries_length 
  {t: String} {queries: List (Nat × Nat × Nat)} :
  List.length (check_reachable t queries) = List.length queries :=
sorry 

theorem check_reachable_results_valid 
  {t: String} {queries: List (Nat × Nat × Nat)} :
  ∀ r ∈ check_reachable t queries, r = "Yes" ∨ r = "No" :=
sorry

theorem same_position_always_reachable 
  {t: String} (i: Nat) :
  check_reachable t [(i+1, i+1, 1)] = ["Yes"] :=
sorry

theorem equal_strings_reachable
  {t: String} {l1 l2 leng: Nat} :
  t.data = t.data →
  check_reachable t [(l1, l2, leng)] = ["Yes"] :=
sorry

theorem single_position_reachable
  {t: String} :
  check_reachable t [(1, 1, 1)] = ["Yes"] :=
sorry
-- </vc-theorems>