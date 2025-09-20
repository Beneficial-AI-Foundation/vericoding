-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_pattern_occurrences (keyword pattern : String) (queries : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_pattern_result_properties (keyword pattern : String) (queries : List Nat)
  (h1 : keyword.length > 0) (h2 : pattern.length > 0) :
  let result := count_pattern_occurrences keyword pattern queries
  (result.length = queries.length) ∧ 
  (∀ x ∈ result, x ≥ 0) :=
  sorry

theorem count_pattern_monotonic (keyword pattern : String) (query : Nat)
  (h1 : keyword.length > 0) (h2 : pattern.length > 0) :
  let result1 := count_pattern_occurrences keyword pattern [query]
  let result2 := count_pattern_occurrences keyword pattern [query + keyword.length]
  List.head! result2 ≥ List.head! result1 := 
  sorry

theorem empty_pattern_error (keyword : String) (pattern : String) (queries : List Nat)
  (h1 : keyword.length > 0) (h2 : pattern.length = 0) (h3 : queries.length > 0) :
  ¬∃ result, result = count_pattern_occurrences keyword pattern queries :=
  sorry

theorem pattern_equals_keyword_bound (keyword : String) (queries : List Nat)
  (h1 : keyword.length > 0) (h2 : queries.length > 0) :
  let result := count_pattern_occurrences keyword keyword queries
  ∀ (r q : Nat), r ∈ result → q ∈ queries → 
  r ≤ q / keyword.length + 1 :=
  sorry
-- </vc-theorems>