-- <vc-preamble>
def ValidInput (n : Int) (teams : List (Int × Int)) : Prop :=
  n ≥ 2 ∧ teams.length = Int.natAbs n ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    let team := teams[Int.natAbs i]!
    team.1 ≠ team.2) ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    let team_i := teams[Int.natAbs i]!
    (List.range (Int.natAbs n)).filter (fun j => 
      let team_j := teams[j]!
      team_j.1 = team_i.2
    ) |>.length ≤ Int.natAbs n - 1)

def ValidOutput (n : Int) (teams : List (Int × Int)) (result : List (Int × Int)) : Prop :=
  teams.length = Int.natAbs n →
  result.length = Int.natAbs n ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    let res := result[Int.natAbs i]!
    res.1 + res.2 = 2 * (n - 1)) ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    let res := result[Int.natAbs i]!
    res.1 ≥ n - 1) ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    let res := result[Int.natAbs i]!
    res.2 ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < n → 
    let team_i := teams[Int.natAbs i]!
    let res := result[Int.natAbs i]!
    let homeCount := (List.range (Int.natAbs n)).filter (fun j => 
      let team_j := teams[j]!
      team_j.1 = team_i.2
    ) |>.length
    res.1 = (n - 1) + Int.ofNat homeCount ∧
    res.2 = (n - 1) - Int.ofNat homeCount)

@[reducible, simp]
def solve_precond (n : Int) (teams : List (Int × Int)) : Prop :=
  ValidInput n teams
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (teams : List (Int × Int)) (h_precond : solve_precond n teams) : List (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (teams : List (Int × Int)) (result : List (Int × Int)) (h_precond : solve_precond n teams) : Prop :=
  ValidOutput n teams result

theorem solve_spec_satisfied (n : Int) (teams : List (Int × Int)) (h_precond : solve_precond n teams) :
    solve_postcond n teams (solve n teams h_precond) h_precond := by
  sorry
-- </vc-theorems>