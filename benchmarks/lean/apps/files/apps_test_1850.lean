-- <vc-preamble>

def ValidInput (n d : Int) (currentPoints awards : List Int) : Prop :=
  n ≥ 1 ∧ n ≤ 200000 ∧
  d ≥ 1 ∧ d ≤ n ∧
  currentPoints.length = n ∧
  awards.length = n ∧
  d - 1 < currentPoints.length ∧
  (∀ i, 0 ≤ i ∧ i < currentPoints.length - 1 → currentPoints[i]! ≥ currentPoints[i + 1]!) ∧
  (∀ i, 0 ≤ i ∧ i < awards.length - 1 → awards[i]! ≥ awards[i + 1]!)

def CountOvertakenHelper (currentPoints awards : List Int) (d pos usedAwards : Int) : Int :=
  if pos ≥ d - 1 then 0
  else
    let targetScore := currentPoints[Int.natAbs (d - 1)]! + awards[0]!
    let remainingAwards := currentPoints.length - usedAwards
    if remainingAwards > 0 ∧ usedAwards < currentPoints.length ∧ 
       currentPoints[Int.natAbs pos]! + awards[Int.natAbs (currentPoints.length - 1 - usedAwards)]! ≤ targetScore then
      1 + CountOvertakenHelper currentPoints awards d (pos + 1) (usedAwards + 1)
    else
      CountOvertakenHelper currentPoints awards d (pos + 1) usedAwards
termination_by Int.natAbs (d - 1 - pos)

def CountOvertaken (currentPoints awards : List Int) (d : Int) : Int :=
  CountOvertakenHelper currentPoints awards d 0 0

@[reducible, simp]
def solve_precond (n d : Int) (currentPoints awards : List Int) : Prop :=
  ValidInput n d currentPoints awards
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n d : Int) (currentPoints awards : List Int) (h_precond : solve_precond n d currentPoints awards) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n d : Int) (currentPoints awards : List Int) (result : Int) (h_precond : solve_precond n d currentPoints awards) : Prop :=
  1 ≤ result ∧ result ≤ d ∧ result = d - CountOvertaken currentPoints awards d

theorem solve_spec_satisfied (n d : Int) (currentPoints awards : List Int) (h_precond : solve_precond n d currentPoints awards) :
    solve_postcond n d currentPoints awards (solve n d currentPoints awards h_precond) h_precond := by
  sorry
-- </vc-theorems>