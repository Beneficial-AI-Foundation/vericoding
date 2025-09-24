-- <vc-preamble>
@[reducible, simp]
def below_zero_precond (operations : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList
-- </vc-helpers>

-- <vc-definitions>
def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def below_zero_postcond (operations : List Int) (result: (Array Int × Bool)) (h_precond : below_zero_precond (operations)) :=
  let s := result.1
  let result := result.2
  s.size = operations.length + 1 ∧
  s[0]? = some 0 ∧
  (List.range (s.size - 1)).all (fun i => s[i + 1]? = some (s[i]! + operations[i]!)) ∧
  ((result = true) → ((List.range (operations.length)).any (fun i => s[i + 1]! < 0))) ∧
  ((result = false) → s.all (· ≥ 0))

theorem below_zero_spec_satisfied (operations: List Int) (h_precond : below_zero_precond (operations)) :
    below_zero_postcond (operations) (below_zero (operations) h_precond) h_precond := by
  sorry
-- </vc-theorems>