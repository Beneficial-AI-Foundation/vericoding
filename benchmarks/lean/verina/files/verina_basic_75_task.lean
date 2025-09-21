-- <vc-preamble>
@[reducible, simp]
def minArray_precond (a : Array Int) : Prop :=
  a.size > 0
-- </vc-preamble>

-- <vc-helpers>
def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin
-- </vc-helpers>

-- <vc-definitions>
def minArray (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def minArray_postcond (a : Array Int) (result: Int) (h_precond : minArray_precond (a)) :=
  (∀ i : Nat, i < a.size → result <= a[i]!) ∧ (∃ i : Nat, i < a.size ∧ result = a[i]!)

theorem minArray_spec_satisfied (a: Array Int) (h_precond : minArray_precond (a)) :
    minArray_postcond (a) (minArray (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>