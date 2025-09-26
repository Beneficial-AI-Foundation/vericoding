-- <vc-preamble>
def ValidInput (n m : Int) (a : List Int) : Prop :=
  n > 0 ∧ m > 0 ∧ a.length = n.natAbs ∧ ∀ i, 0 ≤ i ∧ i < a.length → a[i]! > 0

def ValidResult (result n : Int) : Prop :=
  1 ≤ result ∧ result ≤ n

def SumCandiesStillNeeded (queue : List (List Int)) : Nat :=
  match queue with
  | [] => 0
  | child :: rest =>
      if child.length == 3 ∧ child[0]! ≥ 0 ∧ child[1]! > 0 then
        let stillNeeded := if child[1]! ≤ child[0]! then 0 else (child[1]! - child[0]!).natAbs
        stillNeeded + SumCandiesStillNeeded rest
      else 0

@[reducible, simp]
def solve_precond (n m : Int) (a : List Int) : Prop :=
  ValidInput n m a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (a : List Int) (h_precond : solve_precond n m a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (a : List Int) (result : Int) (h_precond : solve_precond n m a) : Prop :=
  ValidResult result n

theorem solve_spec_satisfied (n m : Int) (a : List Int) (h_precond : solve_precond n m a) :
    solve_postcond n m a (solve n m a h_precond) h_precond := by
  sorry
-- </vc-theorems>