-- <vc-preamble>
@[reducible, simp]
def replace_precond (arr : Array Int) (k : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc
-- </vc-helpers>

-- <vc-definitions>
def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replace_postcond (arr : Array Int) (k : Int) (result: Array Int) (h_precond : replace_precond (arr) (k)) :=
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))

theorem replace_spec_satisfied (arr: Array Int) (k: Int) (h_precond : replace_precond (arr) (k)) :
    replace_postcond (arr) (k) (replace (arr) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>