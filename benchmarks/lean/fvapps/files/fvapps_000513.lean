-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def perfect_square_range_query (arr : List Nat) (queries : List (Nat × Nat × Nat)) : List String :=
sorry

def is_perfect_square (n : Nat) : Bool :=
sorry

def product_range (arr : List Nat) (s e : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem query_response_format
  (arr : List Nat) (queries : List (Nat × Nat × Nat)) :
  let result := perfect_square_range_query arr queries
  let type_1_count := (queries.filter (fun q => q.fst = 1)).length
  result.length = type_1_count ∧
  result.all (fun r => r = "YES" ∨ r = "NO") :=
sorry

theorem array_update_consistency
  (arr : List Nat) (queries : List (Nat × Nat × Nat)) (i : Nat) (h : i < queries.length) :
  let result := perfect_square_range_query arr queries
  let q := queries[i]'h
  (q.fst = 1 →
    let product := product_range arr (q.2.1 - 1) (q.2.2)
    (result[i]? = some "YES") = is_perfect_square product) :=
sorry

theorem single_element_range
  (arr : List Nat) (i : Nat) (h : i < arr.length) :
  let queries := List.range arr.length |>.map (fun i => (1, i+1, i+1))
  let result := perfect_square_range_query arr queries
  result[i]? = some (if is_perfect_square (arr[i]'h) then "YES" else "NO") :=
sorry
-- </vc-theorems>