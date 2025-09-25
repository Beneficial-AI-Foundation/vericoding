-- <vc-preamble>
@[reducible, simp]
def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)

theorem swap_spec_satisfied (arr: Array Int) (i: Int) (j: Int) (h_precond : swap_precond (arr) (i) (j)) :
    swap_postcond (arr) (i) (j) (swap (arr) (i) (j) h_precond) h_precond := by
  sorry
-- </vc-theorems>