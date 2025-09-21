-- <vc-preamble>
def IsValidWorkSelection (N K C : Nat) (S : String) (selection : List Nat) : Prop :=
  S.length = N ∧
  selection.length = K ∧
  (∀ day ∈ selection, day < N ∧ day < S.length ∧ S.data[day]! = 'o') ∧
  (∀ day1 ∈ selection, ∀ day2 ∈ selection, day1 ≠ day2 → 
      day1 + C < day2 ∨ day2 + C < day1)

@[reducible, simp]
def solve_precond (N K C : Nat) (S : String) : Prop :=
  N > 0 ∧
  K > 0 ∧
  K ≤ N ∧
  S.length = N ∧
  (∀ i, i < S.length → S.data[i]! = 'o' ∨ S.data[i]! = 'x') ∧
  ((List.range S.length).filter (fun i => S.data[i]! = 'o')).length ≥ K ∧
  ∃ validSelection, IsValidWorkSelection N K C S validSelection
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N K C : Nat) (S : String) (h_precond : solve_precond N K C S) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N K C : Nat) (S : String) (result : List Nat) (h_precond : solve_precond N K C S) : Prop :=
  (∀ i, i < result.length → 1 ≤ result[i]! ∧ result[i]! ≤ N) ∧
  (∀ i, i < result.length → S.data[result[i]! - 1]! = 'o') ∧
  (∀ i j, i < j ∧ j < result.length → result[i]! < result[j]!) ∧
  result.length ≤ K

theorem solve_spec_satisfied (N K C : Nat) (S : String) (h_precond : solve_precond N K C S) :
    solve_postcond N K C S (solve N K C S h_precond) h_precond := by
  sorry
-- </vc-theorems>