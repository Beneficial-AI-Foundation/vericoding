-- <vc-preamble>
def ValidGrid (grid: List (List Int)) (n: Int) (m: Int) : Prop :=
  grid.length = n.natAbs ∧ n > 0 ∧ m > 0 ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    match grid[i.natAbs]? with
    | some row => row.length = m.natAbs
    | none => False) ∧
  (∀ i j, 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < m → 
    match grid[i.natAbs]? with
    | some row => 
      match row[j.natAbs]? with
      | some val => val = 0 ∨ val = 1
      | none => False
    | none => False)

def ValidQueries (queries: List (Int × Int)) (q: Int) (n: Int) (m: Int) : Prop :=
  queries.length = q.natAbs ∧ q ≥ 0 ∧
  (∀ k, 0 ≤ k ∧ k < q → 
    match queries[k.natAbs]? with
    | some query => 1 ≤ query.1 ∧ query.1 ≤ n ∧ 1 ≤ query.2 ∧ query.2 ≤ m
    | none => False)

def ConsHelper (l: List Int) (index: Nat) (current: Int) (maxSoFar: Int) : Int :=
  if index ≥ l.length then maxSoFar
  else 
    match l[index]? with
    | some val =>
      if val = 1 then
        let newCurrent := current + 1
        let newMax := if newCurrent > maxSoFar then newCurrent else maxSoFar
        ConsHelper l (index + 1) newCurrent newMax
      else
        ConsHelper l (index + 1) 0 maxSoFar
    | none => maxSoFar

def cons (l: List Int) : Int :=
  ConsHelper l 0 0 0

def MaxInSeq (s: List Int) : Int :=
  match s with
  | [] => 0
  | [x] => x
  | x :: xs => 
    let rest := MaxInSeq xs
    if x > rest then x else rest

def ComputeScore (grid: List (List Int)) : Int :=
  let rowScores := grid.map cons
  MaxInSeq rowScores

@[reducible, simp]
def solve_precond (n m q : Int) (grid : List (List Int)) (queries : List (Int × Int)) : Prop :=
  ValidGrid grid n m ∧ ValidQueries queries q n m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m q : Int) (grid : List (List Int)) (queries : List (Int × Int)) (h_precond : solve_precond n m q grid queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m q : Int) (grid : List (List Int)) (queries : List (Int × Int)) (results : List Int) (h_precond : solve_precond n m q grid queries) : Prop :=
  results.length = q.natAbs

theorem solve_spec_satisfied (n m q : Int) (grid : List (List Int)) (queries : List (Int × Int)) (h_precond : solve_precond n m q grid queries) :
    solve_postcond n m q grid queries (solve n m q grid queries h_precond) h_precond := by
  sorry
-- </vc-theorems>