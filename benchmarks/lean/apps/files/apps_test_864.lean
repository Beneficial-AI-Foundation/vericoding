-- <vc-preamble>
def countPackages (foodTypes : List Int) (targetType : Int) : Int :=
  match foodTypes with
  | [] => 0
  | head :: tail => 
    if head = targetType then 1 + countPackages tail targetType
    else countPackages tail targetType

def countTotalParticipants (foodTypes : List Int) (days : Int) (currentType : Nat) : Int :=
  if currentType > 100 then 0
  else
    let packagesOfThisType := countPackages foodTypes (Int.ofNat currentType)
    let participantsForThisType := if days > 0 then packagesOfThisType / days else 0
    participantsForThisType + countTotalParticipants foodTypes days (currentType + 1)
termination_by (101 - currentType)

def possible (n : Int) (foodTypes : List Int) (days : Int) : Bool :=
  if days = 0 then true
  else
    let totalParticipants := countTotalParticipants foodTypes days 1
    totalParticipants ≥ n

@[reducible, simp]
def solve_precond (n m : Int) (foodTypes : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧
  1 ≤ m ∧ m ≤ 100 ∧
  foodTypes.length = Int.natAbs m ∧
  ∀ i, 0 ≤ i ∧ i < foodTypes.length → 1 ≤ foodTypes[i]! ∧ foodTypes[i]! ≤ 100
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (foodTypes : List Int) (h_precond : solve_precond n m foodTypes) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (foodTypes : List Int) (result : Int) (h_precond : solve_precond n m foodTypes) : Prop :=
  result ≥ 0 ∧
  result ≤ m ∧
  (result > 0 → possible n foodTypes result) ∧
  ¬possible n foodTypes (result + 1) ∧
  ∀ d, d > result → ¬possible n foodTypes d

theorem solve_spec_satisfied (n m : Int) (foodTypes : List Int) (h_precond : solve_precond n m foodTypes) :
    solve_postcond n m foodTypes (solve n m foodTypes h_precond) h_precond := by
  sorry
-- </vc-theorems>