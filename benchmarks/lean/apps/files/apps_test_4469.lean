-- <vc-preamble>

def ValidInput (queries: List (Char × Int)) : Prop :=
  queries.length > 0 ∧
  (∀ i, 0 ≤ i ∧ i < queries.length → (queries[i]!).1 = 'L' ∨ (queries[i]!).1 = 'R' ∨ (queries[i]!).1 = '?') ∧
  (∀ i, 0 ≤ i ∧ i < queries.length → (queries[i]!).2 > 0) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < queries.length ∧ ((queries[i]!).1 = 'L' ∨ (queries[i]!).1 = 'R') ∧ ((queries[j]!).1 = 'L' ∨ (queries[j]!).1 = 'R') → (queries[i]!).2 ≠ (queries[j]!).2) ∧
  (∀ i, 0 ≤ i ∧ i < queries.length ∧ (queries[i]!).1 = '?' → 
      ∃ j, 0 ≤ j ∧ j < i ∧ ((queries[j]!).1 = 'L' ∨ (queries[j]!).1 = 'R') ∧ (queries[j]!).2 = (queries[i]!).2) ∧
  (∃ i, 0 ≤ i ∧ i < queries.length ∧ (queries[i]!).1 = '?')

structure BookshelfState where
  positions : Int → Option Int
  head : Int
  tail : Int

def SimulateQueries (queries: List (Char × Int)) (query_idx: Nat) : BookshelfState :=
  { positions := fun _ => none, head := 0, tail := 0 }

def ComputeMinRemovals (queries: List (Char × Int)) (query_idx: Nat) : Int :=
  if h : query_idx < queries.length ∧ (queries[query_idx]!).1 = '?' then
    let book_id := (queries[query_idx]!).2
    let state := SimulateQueries queries query_idx
    match state.positions book_id with
    | some pos => 
        let left_removals := pos - state.head
        let right_removals := state.tail - pos
        let min_removals := min left_removals right_removals
        min_removals - 1
    | none => 0
  else 0

def ValidOutput (queries: List (Char × Int)) (results: List Int) : Prop :=
  results.length = (queries.filter (fun q => q.1 = '?')).length ∧
  (∀ i, 0 ≤ i ∧ i < results.length → results[i]! ≥ 0) ∧
  (∀ r_idx, 0 ≤ r_idx ∧ r_idx < results.length → 
      ∃ q_idx, q_idx < queries.length ∧ (queries[q_idx]!).1 = '?' ∧
      results[r_idx]! = ComputeMinRemovals queries q_idx) ∧
  (∀ q_idx, q_idx < queries.length ∧ (queries[q_idx]!).1 = '?' →
      ∃ r_idx, 0 ≤ r_idx ∧ r_idx < results.length ∧
      results[r_idx]! = ComputeMinRemovals queries q_idx)

@[reducible, simp]
def solve_precond (queries: List (Char × Int)) : Prop :=
  ValidInput queries
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (queries: List (Char × Int)) (h_precond : solve_precond queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (queries: List (Char × Int)) (results: List Int) (h_precond : solve_precond queries) : Prop :=
  ValidOutput queries results

theorem solve_spec_satisfied (queries: List (Char × Int)) (h_precond : solve_precond queries) :
    solve_postcond queries (solve queries h_precond) h_precond := by
  sorry
-- </vc-theorems>