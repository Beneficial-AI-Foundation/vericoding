-- <vc-preamble>
/- Helper spec function to find minimum value in a sequence -/
def minSpec (seq : List Int) : Int :=
  if h : seq.length = 1 then
    seq[0]!
  else if seq.length = 0 then
    0
  else
    let laterMin := minSpec (seq.tail)
    if seq[0]! ≤ laterMin then
      seq[0]!
    else
      laterMin
termination_by seq.length

@[reducible, simp]
def secondSmallest_precond (numbers : Array Int) :=
  numbers.size ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def secondSmallest (numbers : Array Int) (h_precond : secondSmallest_precond (numbers)) : (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def secondSmallest_postcond (numbers : Array Int) (indices : Nat × Nat) (h_precond : secondSmallest_precond (numbers)) :=
  (∀ k : Nat, k < numbers.size → k ≠ indices.1 → numbers[indices.1]! = minSpec (numbers.toList) → numbers[k]! ≥ numbers[indices.2]!) ∧
  (∃ k : Nat, k < numbers.size ∧ k ≠ indices.1 ∧ numbers[k]! = numbers[indices.2]!)

theorem secondSmallest_spec_satisfied (numbers : Array Int) (h_precond : secondSmallest_precond (numbers)) :
    secondSmallest_postcond (numbers) (secondSmallest (numbers) h_precond) h_precond := by
  sorry
-- </vc-theorems>