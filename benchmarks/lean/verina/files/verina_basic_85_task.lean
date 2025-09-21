-- <vc-preamble>
@[reducible, simp]
def reverse_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr
-- </vc-helpers>

-- <vc-definitions>
def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def reverse_postcond (a : Array Int) (result: Array Int) (h_precond : reverse_precond (a)) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → result[i]! = a[a.size - 1 - i]!)

theorem reverse_spec_satisfied (a: Array Int) (h_precond : reverse_precond (a)) :
    reverse_postcond (a) (reverse (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>