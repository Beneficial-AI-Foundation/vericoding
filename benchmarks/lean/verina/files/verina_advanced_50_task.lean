-- <vc-preamble>
@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Array Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)

theorem mergeSorted_spec_satisfied (a1: Array Nat) (a2: Array Nat) :
    mergeSorted_postcond (a1) (a2) (mergeSorted (a1) (a2)) := by
  sorry
-- </vc-theorems>