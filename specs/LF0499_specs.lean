-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_string_queries (s : String) (queries : List Query) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_string_queries_no_queries (s : String) :
  process_string_queries s [] = [] := sorry

theorem process_string_queries_only_substring_queries (s : String) (queries : List Query) 
  (h : ∀ q ∈ queries, q.queryType = 2 ∧ q.position ≤ s.length) :
  let result := process_string_queries s queries
  result.length = queries.length ∧ 
  (∀ x ∈ result, 0 ≤ x ∧ x ≤ 26) := sorry 

theorem process_string_queries_only_change_queries (s : String) (queries : List Query)
  (h : ∀ q ∈ queries, q.queryType = 1 ∧ q.position ≤ s.length) :
  process_string_queries s queries = [] := sorry

theorem process_string_queries_single_char (s : String) (i : Nat)
  (h1 : s.length > 0)
  (h2 : i ≤ s.length) :
  process_string_queries s [⟨2, i, (i, 'a')⟩] = [1] := sorry

theorem process_string_queries_change_then_query (s : String) (pos : Nat) (new_char : Char)
  (h1 : s.length > 0)
  (h2 : pos ≤ s.length) :
  process_string_queries s [⟨1, pos, (pos, new_char)⟩, ⟨2, pos, (pos, new_char)⟩] = [1] := sorry

/-
info: [3, 1, 5]
-/
-- #guard_msgs in
-- #eval process_string_queries "abcdbbd" [(2, 3, 6), (1, 5, "z"), (2, 1, 1), (1, 4, "a"), (1, 7, "d"), (2, 1, 7)]

/-
info: [3, 3]
-/
-- #guard_msgs in
-- #eval process_string_queries "abc" [(2, 1, 3), (1, 2, "d"), (2, 1, 3)]

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval process_string_queries "aaa" [(2, 1, 3), (1, 2, "b"), (2, 1, 3)]
-- </vc-theorems>