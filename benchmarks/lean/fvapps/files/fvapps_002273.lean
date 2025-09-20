-- <vc-preamble>
def isSorted {α : Type u} [Ord α] [LE α] (xs : List α) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ isSorted (y :: rest)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_ops_to_sort {α : Type u} [Ord α] (arr : List α) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem translation_invariant (arr : List Int) (k : Int) :
  min_ops_to_sort arr = min_ops_to_sort (arr.map (fun x => x + k)) :=
sorry
-- </vc-theorems>