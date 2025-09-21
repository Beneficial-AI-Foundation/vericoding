-- <vc-preamble>
def ValidInput (testCases : List (Int × Int × List (Int × Int))) : Prop :=
  testCases.length ≥ 0 ∧
  ∀ i, i < testCases.length → 
    let (n, x, operations) := testCases[i]!
    n ≥ 1 ∧ 1 ≤ x ∧ x ≤ n ∧ operations.length ≥ 0 ∧
    (∀ j, j < operations.length → 
      let (l, r) := operations[j]!
      1 ≤ l ∧ l ≤ r ∧ r ≤ n)

def computeFinalBoundsHelper (left right : Int) (operations : List (Int × Int)) (index : Nat) : Int × Int :=
  if index ≥ operations.length then (left, right)
  else
    let (l, r) := operations[index]!
    let newLeft := min left l
    let newRight := max right r
    computeFinalBoundsHelper newLeft newRight operations (index + 1)

def computeFinalBounds (x : Int) (operations : List (Int × Int)) : Int × Int :=
  computeFinalBoundsHelper x x operations 0

def ValidResults (testCases : List (Int × Int × List (Int × Int))) (results : List Int) : Prop :=
  ValidInput testCases →
  results.length = testCases.length ∧
  ∀ i, i < testCases.length → 
    let (n, x, operations) := testCases[i]!
    let finalBounds := computeFinalBounds x operations
    results[i]! = finalBounds.2 - finalBounds.1 + 1 ∧
    finalBounds.1 ≤ x ∧ x ≤ finalBounds.2 ∧
    results[i]! ≥ 1 ∧
    1 ≤ finalBounds.1 ∧ finalBounds.1 ≤ finalBounds.2 ∧ finalBounds.2 ≤ n

@[reducible, simp]
def solve_precond (testCases : List (Int × Int × List (Int × Int))) : Prop :=
  ValidInput testCases
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (testCases : List (Int × Int × List (Int × Int))) (h_precond : solve_precond testCases) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (testCases : List (Int × Int × List (Int × Int))) (results : List Int) (h_precond : solve_precond testCases) : Prop :=
  ValidResults testCases results

theorem solve_spec_satisfied (testCases : List (Int × Int × List (Int × Int))) (h_precond : solve_precond testCases) :
    solve_postcond testCases (solve testCases h_precond) h_precond := by
  sorry
-- </vc-theorems>