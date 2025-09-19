-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_reachability (n q : Nat) (arr : List Nat) (queries : List (Nat × Nat)) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reachability_output_length (n q : Nat) (arr : List Nat) (queries : List (Nat × Nat)) :
  queries.length = q → (check_reachability n q arr queries).length = q :=
sorry

theorem reachability_output_valid (n q : Nat) (arr : List Nat) (queries : List (Nat × Nat)) :
  ∀ x ∈ check_reachability n q arr queries, x = "Shi" ∨ x = "Fou" :=
sorry

theorem zero_node_not_self_reachable (n : Nat) (arr : List Nat) (i : Nat) (h : i < n) 
  (hArr : arr.length = n) (hZero : arr[i] = 0) :
  check_reachability n 1 arr [(i+1, i+1)] = ["Fou"] :=
sorry

theorem single_element_all_bits_reachable :
  let arr := [2^20 - 1]
  check_reachability 1 1 arr [(1,1)] = ["Shi"] :=
sorry

theorem single_element_no_bits_unreachable :
  let arr := [0]
  check_reachability 1 1 arr [(1,1)] = ["Fou"] :=
sorry
-- </vc-theorems>