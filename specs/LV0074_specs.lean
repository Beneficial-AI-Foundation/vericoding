-- <vc-preamble>
@[reducible, simp]
def task_code_precond (sequence : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def task_code (sequence : List Int) (h_precond : task_code_precond (sequence)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def task_code_postcond (sequence : List Int) (result: Int) (h_precond : task_code_precond (sequence)) : Prop :=
  let subArrays :=
    List.range (sequence.length + 1) |>.flatMap (fun start =>
      List.range (sequence.length - start + 1) |>.map (fun len =>
        sequence.drop start |>.take len))
  let subArraySums := subArrays.filter (· ≠ []) |>.map (·.sum)
  subArraySums.contains result ∧ subArraySums.all (· ≤ result)

theorem task_code_spec_satisfied (sequence: List Int) (h_precond : task_code_precond (sequence)) :
    task_code_postcond (sequence) (task_code (sequence) h_precond) h_precond := by
  sorry
-- </vc-theorems>