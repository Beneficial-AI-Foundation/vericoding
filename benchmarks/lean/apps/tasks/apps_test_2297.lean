-- <vc-preamble>
@[reducible, simp]
def ValidQuery (query : Int × Int) : Prop :=
  query.1 ≥ 1 ∧ query.1 ≤ query.2

@[reducible, simp]
def ValidInput (queries : List (Int × Int)) : Prop :=
  ∀ i, 0 ≤ i ∧ i < queries.length → ValidQuery (queries[i]!)

def ArrayElement (i : Int) : Int :=
  i * (if i % 2 = 1 then -1 else 1)

def RangeSum : Int → Int → Int
  | l, r => if l > r then 0 else ArrayElement l + RangeSum (l + 1) r
  termination_by l r => Int.natAbs (r - l + 1)

def PrefixSum (k : Int) : Int :=
  if k % 2 = 0 then k / 2 else -(k + 1) / 2

@[reducible, simp]
def CorrectResult (queries : List (Int × Int)) (results : List Int) : Prop :=
  results.length = queries.length ∧
  ∀ i, 0 ≤ i ∧ i < queries.length → results[i]! = PrefixSum (queries[i]!).2 - PrefixSum ((queries[i]!).1 - 1)

@[reducible, simp]
def solve_precond (queries : List (Int × Int)) : Prop :=
  ValidInput queries
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (queries : List (Int × Int)) (h_precond : solve_precond queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (queries : List (Int × Int)) (result : List Int) (h_precond : solve_precond queries) : Prop :=
  CorrectResult queries result

theorem solve_spec_satisfied (queries : List (Int × Int)) (h_precond : solve_precond queries) :
    solve_postcond queries (solve queries h_precond) h_precond := by
  sorry
-- </vc-theorems>