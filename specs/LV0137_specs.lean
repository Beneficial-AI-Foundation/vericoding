-- <vc-preamble>
@[reducible, simp]
def CountLessThan_precond (numbers : Array Int) (threshold : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def countLessThan (numbers : Array Int) (threshold : Int) : Nat :=
  let rec count (i : Nat) (acc : Nat) : Nat :=
    if i < numbers.size then
      let new_acc := if numbers[i]! < threshold then acc + 1 else acc
      count (i + 1) new_acc
    else
      acc
  count 0 0
-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : Array Int) (threshold : Int) (h_precond : CountLessThan_precond (numbers) (threshold)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def CountLessThan_postcond (numbers : Array Int) (threshold : Int) (result: Nat) (h_precond : CountLessThan_precond (numbers) (threshold)) :=
  result - numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 = 0 ∧
  numbers.foldl (fun count n => if n < threshold then count + 1 else count) 0 - result = 0

theorem CountLessThan_spec_satisfied (numbers: Array Int) (threshold: Int) (h_precond : CountLessThan_precond (numbers) (threshold)) :
    CountLessThan_postcond (numbers) (threshold) (CountLessThan (numbers) (threshold) h_precond) h_precond := by
  sorry
-- </vc-theorems>