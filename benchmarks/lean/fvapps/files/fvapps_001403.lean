-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_toffee_queries (queries : List String) : List Nat := sorry

theorem process_toffee_queries_valid_output (queries : List String) :
  let results := process_toffee_queries queries
  -- Results length equals number of type 2 queries
  results.length = (queries.filter (fun q => q.take 1 = "2")).length ∧ 
  -- All results are non-negative
  results.all (fun r => r ≥ 0) := by
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_toffee_queries_accumulative 
  (type1_queries : List String)
  (h1 : type1_queries.all (fun q => q.take 1 = "1")) :
  let all_queries := type1_queries ++ ["2 1 5 a"]
  let results := process_toffee_queries all_queries
  -- Last result equals count of type 1 queries
  results.getLast! = type1_queries.length := by
  sorry
-- </vc-theorems>