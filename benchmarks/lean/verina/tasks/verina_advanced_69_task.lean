-- <vc-preamble>
@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  List.Pairwise (· < ·) xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) (h_precond : searchInsert_precond (xs) (target)) : Prop :=
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly

theorem searchInsert_spec_satisfied (xs: List Int) (target: Int) (h_precond : searchInsert_precond (xs) (target)) :
    searchInsert_postcond (xs) (target) (searchInsert (xs) (target) h_precond) h_precond := by
  sorry
-- </vc-theorems>