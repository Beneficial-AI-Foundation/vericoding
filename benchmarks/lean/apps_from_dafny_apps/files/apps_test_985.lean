-- <vc-preamble>
-- <vc-preamble>
def ValidInput (positions : List (Int × Int)) : Prop :=
  positions.length ≥ 1 ∧ positions.length ≤ 200000 ∧
  (∀ i, 0 ≤ i ∧ i < positions.length → 
      1 ≤ positions[i]!.1 ∧ positions[i]!.1 ≤ 1000 ∧ 1 ≤ positions[i]!.2 ∧ positions[i]!.2 ≤ 1000) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < positions.length → positions[i]! ≠ positions[j]!)

def CountAttackingPairs (positions : List (Int × Int)) (h : ValidInput positions) : Int :=
  sorry

def ValidOutput (positions : List (Int × Int)) (result : Int) (h : ValidInput positions) : Prop :=
  result = CountAttackingPairs positions h ∧ result ≥ 0

@[reducible, simp]
def solve_precond (positions : List (Int × Int)) : Prop :=
  ValidInput positions
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (positions : List (Int × Int)) (h_precond : solve_precond positions) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (positions : List (Int × Int)) (result: Int) (h_precond : solve_precond positions) : Prop :=
  ValidOutput positions result h_precond ∧ result ≥ 0

theorem solve_spec_satisfied (positions : List (Int × Int)) (h_precond : solve_precond positions) :
    solve_postcond positions (solve positions h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
