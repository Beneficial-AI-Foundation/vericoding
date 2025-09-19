-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_char_frequency (height : Nat) (s : String) (queries : List (String × Char)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_row_matches_string {height : Nat} {s : String} {queries : List (String × Char)} 
  (h1 : height > 0) (h2 : s.length > 0) (h3 : queries.length > 0)
  (h4 : ∀ q ∈ queries, q.1 = "1" ∧ q.2.isUpper) :
  ∀ (i : Nat) (hi : i < queries.length),
    let query := queries[i]'hi
    let result := find_char_frequency height s queries
    let count := result[i]'(by 
      have : result.length = queries.length := sorry
      exact this ▸ hi)
    count = (List.filter (· = query.2) (s.take 1).toList).length :=
sorry

theorem counts_nonnegative {height : Nat} {s : String} {queries : List (String × Char)}
  (h1 : height > 0) (h2 : s.length > 0) (h3 : queries.length > 0)
  (h4 : ∀ q ∈ queries, q.2.isUpper) :
  let result := find_char_frequency height s queries
  (∀ x ∈ result, x ≥ 0) ∧ result.length = queries.length :=
sorry

theorem known_pattern {height : Nat} {s : String}
  (h1 : height > 0) (h2 : s = "ABC") :
  find_char_frequency height s [("1", 'A'), ("2", 'B'), ("3", 'C')] = [1, 1, 1] :=
sorry
-- </vc-theorems>