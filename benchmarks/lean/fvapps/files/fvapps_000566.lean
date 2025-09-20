-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveBracketSequence (s : String) (queries : List Nat) : List Int := sorry

theorem arbitrary_brackets_results_valid 
  (s : String) 
  (queries : List Nat) 
  (h1 : s.length > 0)
  (h2 : queries.length > 0)
  (h3 : ∀ c ∈ s.data, c = '(' ∨ c = ')')
  (h4 : ∀ q ∈ queries, 0 < q ∧ q ≤ s.length) :
  let result := solveBracketSequence s queries
  ∀ r ∈ result, -1 ≤ r ∧ r ≤ s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arbitrary_brackets_positions_valid
  (s : String)
  (queries : List Nat)
  (h1 : s.length > 0)
  (h2 : queries.length > 0)
  (h3 : ∀ c ∈ s.data, c = '(' ∨ c = ')')
  (h4 : ∀ q ∈ queries, 0 < q ∧ q ≤ s.length) :
  let result := solveBracketSequence s queries
  ∀ (q : Nat) (r : Int),
    q ∈ queries →
    r ∈ result →
    r ≠ -1 →
    s.data[r.toNat - 1]? = some ')' ∧ r > q := sorry

theorem all_open_brackets_no_matches
  (s : String)
  (queries : List Nat)
  (h1 : s.length > 0)
  (h2 : queries.length > 0)
  (h3 : ∀ c ∈ s.data, c = '(')
  (h4 : ∀ q ∈ queries, 0 < q ∧ q ≤ s.length) :
  let result := solveBracketSequence s queries
  ∀ r ∈ result, r = -1 := sorry

theorem all_close_brackets_no_matches
  (s : String)
  (queries : List Nat)
  (h1 : s.length > 0)
  (h2 : queries.length > 0)
  (h3 : ∀ c ∈ s.data, c = ')')
  (h4 : ∀ q ∈ queries, 0 < q ∧ q ≤ s.length) :
  let result := solveBracketSequence s queries
  ∀ r ∈ result, r = -1 := sorry
-- </vc-theorems>