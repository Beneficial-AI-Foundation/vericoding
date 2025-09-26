import Mathlib
-- <vc-preamble>
def ValidQuery (query: Int × Int × Int) : Prop :=
  query.1 > 0 ∧ query.2.1 > 0 ∧ query.2.2 > 0

def MinCostForQuery (n a b : Int) : Int :=
  if n > 0 ∧ a > 0 ∧ b > 0 then
    if n % 2 = 0 then
      if n * a ≤ (n / 2) * b then n * a else (n / 2) * b
    else
      if n * a ≤ (n / 2) * b + a then n * a else (n / 2) * b + a
  else 0

@[reducible, simp]
def solve_precond (queries : List (Int × Int × Int)) : Prop :=
  ∀ i, i < queries.length → ValidQuery (queries.get! i)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Compute the result for a single query, matching the postcondition's formula. -/
def computeCost (q : Int × Int × Int) : Int :=
  let n := q.1
  let a := q.2.1
  let b := q.2.2
  if n % 2 = 0 then
    if n * a ≤ (n / 2) * b then n * a else (n / 2) * b
  else
    if n * a ≤ (n / 2) * b + a then n * a else (n / 2) * b + a

-- LLM HELPER
lemma List.get!_map_eq {α β} [Inhabited α] [Inhabited β] (f : α → β) :
  ∀ (l : List α) (i : Nat), i < l.length → (l.map f).get! i = f (l.get! i) := by
  intro l
  induction l with
  | nil =>
      intro i h; cases h
  | cons x xs ih =>
      intro i h
      cases i with
      | zero =>
          simp
      | succ i' =>
          have hi : i' < xs.length := Nat.lt_of_succ_lt_succ h
          simpa using ih i' hi
-- </vc-helpers>

-- <vc-definitions>
def solve (queries : List (Int × Int × Int)) (h_precond : solve_precond queries) : List Int :=
  queries.map computeCost
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (queries : List (Int × Int × Int)) (results : List Int) (h_precond : solve_precond queries) : Prop :=
  results.length = queries.length ∧
  ∀ i, i < queries.length →
    let n := (queries.get! i).1
    let a := (queries.get! i).2.1
    let b := (queries.get! i).2.2
    results.get! i = (if n % 2 = 0 then
      if n * a ≤ (n / 2) * b then n * a else (n / 2) * b
    else
      if n * a ≤ (n / 2) * b + a then n * a else (n / 2) * b + a)

theorem solve_spec_satisfied (queries : List (Int × Int × Int)) (h_precond : solve_precond queries) :
    solve_postcond queries (solve queries h_precond) h_precond := by
  constructor
  · simp [solve, computeCost]
  · intro i hi
    have h := List.get!_map_eq computeCost queries i hi
    simpa [solve, computeCost] using h
-- </vc-theorems>
