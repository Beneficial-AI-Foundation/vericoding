-- <vc-preamble>
def ValidInput (n m : Int) (A : List Int) (queries : List Int) : Prop :=
  A.length = n.natAbs ∧ queries.length = m.natAbs ∧ n ≥ 1 ∧ m ≥ 1 ∧
  ∀ i, 0 ≤ i ∧ i < m → 1 ≤ queries[i.natAbs]! ∧ queries[i.natAbs]! ≤ n

def DistinctCount (A : List Int) (start : Nat) : Nat :=
  let suffix := A.drop start
  let rec countDistinct (l : List Int) (seen : List Int) : Nat :=
    match l with
    | [] => seen.length
    | x :: xs => 
      if seen.contains x then countDistinct xs seen
      else countDistinct xs (x :: seen)
  countDistinct suffix []

@[reducible, simp]
def solve_precond (n m : Int) (A : List Int) (queries : List Int) : Prop :=
  ValidInput n m A queries
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (A : List Int) (queries : List Int) (h_precond : solve_precond n m A queries) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (A : List Int) (queries : List Int) (result : List Int) (h_precond : solve_precond n m A queries) : Prop :=
  result.length = m.natAbs ∧ 
  ∀ i, 0 ≤ i ∧ i < m → result[i.natAbs]! = Int.ofNat (DistinctCount A ((queries[i.natAbs]! - 1).natAbs))

theorem solve_spec_satisfied (n m : Int) (A : List Int) (queries : List Int) (h_precond : solve_precond n m A queries) :
    solve_postcond n m A queries (solve n m A queries h_precond) h_precond := by
  sorry
-- </vc-theorems>