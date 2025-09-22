-- <vc-preamble>
def ValidInput (testCases : List (List Int)) : Prop :=
  ∀ i, 0 ≤ i ∧ i < testCases.length → 
    testCases[i]!.length ≥ 1 ∧ 
    ∀ j, 0 ≤ j ∧ j < testCases[i]!.length → testCases[i]![j]! ≥ 1

def ValidResults (results : List String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < results.length → 
    results[i]! = "First" ∨ results[i]! = "Second"

def CountLeadingOnes (piles : List Int) : Nat :=
  match piles with
  | [] => 0
  | x :: xs => if x ≠ 1 then 0 else 1 + CountLeadingOnes xs

def CorrectGameResult (piles : List Int) (result : String) : Prop :=
  piles.length ≥ 1 ∧ 
  (∀ j, 0 ≤ j ∧ j < piles.length → piles[j]! ≥ 1) ∧
  (result = "First" ∨ result = "Second") ∧
  let onesCount := (piles.filter (· = 1)).length
  let allOnes := (onesCount = piles.length)
  let leadingOnes := CountLeadingOnes piles
  if allOnes then
    (if onesCount % 2 = 1 then result = "First" else result = "Second")
  else
    (if leadingOnes % 2 = 1 then result = "Second" else result = "First")

@[reducible, simp]
def solve_precond (testCases : List (List Int)) : Prop :=
  ValidInput testCases
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (testCases : List (List Int)) (h_precond : solve_precond testCases) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (testCases : List (List Int)) (results : List String) (h_precond : solve_precond testCases) : Prop :=
  results.length = testCases.length ∧
  ValidResults results ∧
  ∀ i, 0 ≤ i ∧ i < testCases.length → CorrectGameResult testCases[i]! results[i]!

theorem solve_spec_satisfied (testCases : List (List Int)) (h_precond : solve_precond testCases) :
    solve_postcond testCases (solve testCases h_precond) h_precond := by
  sorry
-- </vc-theorems>