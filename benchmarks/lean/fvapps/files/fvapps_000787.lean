-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_subarray_query (n : Nat) (arr : List Int) (queries : List Nat) : List Int := sorry

def list_maximum (l : List Int) : Int := 
  match l with
  | [] => 0
  | x::xs => (List.foldl max x xs)
-- </vc-definitions>

-- <vc-theorems>
theorem length_and_types {n : Nat} {arr : List Int} {queries : List Nat} 
  (h1 : arr.length > 0) 
  (h2 : arr.length ≤ 5)  
  (h3 : queries.length > 0)
  (h4 : queries.length ≤ 3)
  (h5 : ∀ x ∈ arr, -100 ≤ x ∧ x ≤ 100)
  (h6 : ∀ q ∈ queries, 1 ≤ q ∧ q ≤ 15) :
  let result := solve_max_subarray_query n arr queries
  result.length = queries.length := 
sorry

theorem max_values {n : Nat} {arr : List Int} {queries : List Nat}
  (h1 : arr.length > 0)
  (h2 : arr.length ≤ 4)
  (h3 : queries.length > 0) 
  (h4 : queries.length ≤ 3)
  (h5 : ∀ x ∈ arr, -100 ≤ x ∧ x ≤ 100)
  (h6 : ∀ q ∈ queries, 1 ≤ q ∧ q ≤ 10) :
  let result := solve_max_subarray_query n arr queries
  ∀ x, x ∈ result → x ≤ list_maximum arr :=
sorry

theorem identical_queries {n : Nat} {arr : List Int}
  (h1 : arr.length > 0)
  (h2 : arr.length ≤ 3) 
  (h3 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10) :
  let queries := List.replicate 3 1
  let result := solve_max_subarray_query n arr queries
  ∀ x y, x ∈ result → y ∈ result → x = y :=
sorry
-- </vc-theorems>