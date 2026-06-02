import Mathlib
-- <vc-preamble>
def ValidInput (positions : List (Int × Int)) : Prop :=
  positions.length ≥ 1 ∧ positions.length ≤ 200000 ∧
  (∀ i, 0 ≤ i ∧ i < positions.length → 
      1 ≤ positions[i]!.1 ∧ positions[i]!.1 ≤ 1000 ∧ 1 ≤ positions[i]!.2 ∧ positions[i]!.2 ≤ 1000) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < positions.length → positions[i]! ≠ positions[j]!)

def CountAttackingPairs (positions : List (Int × Int)) (h : ValidInput positions) : Int :=
  let pairs := (List.range positions.length).foldl (fun acc i =>
    acc ++ (List.range positions.length).map (fun j => (i, j))) []
  Int.ofNat (List.length (List.filter (fun pair =>
    let i := pair.1
    let j := pair.2
    0 ≤ i ∧ i < j ∧ j < positions.length ∧
    (positions[i]!.1 + positions[i]!.2 = positions[j]!.1 + positions[j]!.2 ∨
     positions[i]!.1 - positions[i]!.2 = positions[j]!.1 - positions[j]!.2))
    pairs))

def ValidOutput (positions : List (Int × Int)) (result : Int) (h : ValidInput positions) : Prop :=
  result = CountAttackingPairs positions h ∧ result ≥ 0

@[reducible, simp]
def solve_precond (positions : List (Int × Int)) : Prop :=
  ValidInput positions
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem Count_nonneg {positions : List (Int × Int)} (h : ValidInput positions) : 0 ≤ CountAttackingPairs positions h := by
  dsimp [CountAttackingPairs]
  apply Int.ofNat_nonneg

-- </vc-helpers>

-- <vc-definitions>
def solve (positions : List (Int × Int)) (h_precond : solve_precond positions) : Int :=
  CountAttackingPairs positions h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (positions : List (Int × Int)) (result : Int) (h_precond : solve_precond positions) : Prop :=
  ValidOutput positions result h_precond ∧ result ≥ 0

theorem solve_spec_satisfied (positions : List (Int × Int)) (h_precond : solve_precond positions) :
    solve_postcond positions (solve positions h_precond) h_precond := by
  dsimp [solve, solve_postcond]
  constructor
  · constructor
    · rfl
    · apply Count_nonneg h_precond
  · apply Count_nonneg h_precond

-- </vc-theorems>
