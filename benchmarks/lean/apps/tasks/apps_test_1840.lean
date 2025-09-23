-- <vc-preamble>
def ValidInput (s b : Nat) (attacking_powers : List Nat) (bases : List (Nat × Nat)) : Prop :=
  attacking_powers.length = s ∧ bases.length = b

def SumGoldForSpaceship (attacking_power : Nat) (bases : List (Nat × Nat)) : Nat :=
  match bases with
  | [] => 0
  | (defense, gold) :: rest =>
    if attacking_power ≥ defense then
      gold + SumGoldForSpaceship attacking_power rest
    else
      SumGoldForSpaceship attacking_power rest

def ValidOutput (s : Nat) (attacking_powers : List Nat) (bases : List (Nat × Nat)) (result : List Nat) : Prop :=
  result.length = s ∧
  (∀ i, i < result.length → result[i]! ≥ 0) ∧
  (∀ i, i < s ∧ i < attacking_powers.length → result[i]! = SumGoldForSpaceship attacking_powers[i]! bases)

@[reducible, simp]
def solve_precond (s b : Nat) (attacking_powers : List Nat) (bases : List (Nat × Nat)) : Prop :=
  ValidInput s b attacking_powers bases
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s b : Nat) (attacking_powers : List Nat) (bases : List (Nat × Nat)) (h_precond : solve_precond s b attacking_powers bases) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s b : Nat) (attacking_powers : List Nat) (bases : List (Nat × Nat)) (result : List Nat) (h_precond : solve_precond s b attacking_powers bases) : Prop :=
  ValidOutput s attacking_powers bases result

theorem solve_spec_satisfied (s b : Nat) (attacking_powers : List Nat) (bases : List (Nat × Nat)) (h_precond : solve_precond s b attacking_powers bases) :
    solve_postcond s b attacking_powers bases (solve s b attacking_powers bases h_precond) h_precond := by
  sorry
-- </vc-theorems>