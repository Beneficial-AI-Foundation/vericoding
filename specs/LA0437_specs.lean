-- <vc-preamble>
def ValidBuildingParams (n h a b : Int) : Prop :=
  n ≥ 1 ∧ h ≥ 1 ∧ 1 ≤ a ∧ a ≤ b ∧ b ≤ h

def ValidQuery (query : Int × Int × Int × Int) (n h : Int) : Prop :=
  1 ≤ query.1 ∧ query.1 ≤ n ∧ 1 ≤ query.2.1 ∧ query.2.1 ≤ h ∧
  1 ≤ query.2.2.1 ∧ query.2.2.1 ≤ n ∧ 1 ≤ query.2.2.2 ∧ query.2.2.2 ≤ h

def ValidQueries (queries : List (Int × Int × Int × Int)) (n h : Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < queries.length → ValidQuery (queries.get! i) n h

def abs (x : Int) : Int := if x ≥ 0 then x else -x

def MinTravelTime (t1 f1 t2 f2 a b : Int) : Int :=
  if t1 = t2 then
    abs (f1 - f2)
  else if f1 ≥ a ∧ f1 ≤ b then
    abs (t2 - t1) + abs (f2 - f1)
  else if f1 < a then
    abs (a - f1) + abs (t2 - t1) + abs (f2 - a)
  else
    abs (b - f1) + abs (t2 - t1) + abs (f2 - b)

def CorrectResults (queries : List (Int × Int × Int × Int)) (results : List Int) (a b : Int) : Prop :=
  results.length = queries.length ∧
  ∀ i, 0 ≤ i ∧ i < queries.length →
    let t1 := (queries.get! i).1
    let f1 := (queries.get! i).2.1
    let t2 := (queries.get! i).2.2.1
    let f2 := (queries.get! i).2.2.2
    (results.get! i) = MinTravelTime t1 f1 t2 f2 a b

@[reducible, simp]
def solve_precond (n h a b : Int) (queries : List (Int × Int × Int × Int)) : Prop :=
  ValidBuildingParams n h a b ∧ ValidQueries queries n h
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n h a b : Int) (queries : List (Int × Int × Int × Int)) (h_precond : solve_precond n h a b queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n h a b : Int) (queries : List (Int × Int × Int × Int)) (results : List Int) (h_precond : solve_precond n h a b queries) : Prop :=
  CorrectResults queries results a b

theorem solve_spec_satisfied (n h a b : Int) (queries : List (Int × Int × Int × Int)) (h_precond : solve_precond n h a b queries) :
    solve_postcond n h a b queries (solve n h a b queries h_precond) h_precond := by
  sorry
-- </vc-theorems>