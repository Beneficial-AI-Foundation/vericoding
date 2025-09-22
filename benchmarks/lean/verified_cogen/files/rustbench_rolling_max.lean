-- <vc-preamble>
-- Recursive function to compute maximum of a sequence
def seq_max (a : List Int) : Int :=
  match a with
  | [] => -2147483648  -- i32::MIN equivalent
  | [x] => x
  | x :: xs => max x (seq_max xs)

@[reducible, simp]
def rollingMax_precond (numbers : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rollingMax (numbers : Array Int) (h_precond : rollingMax_precond numbers) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def rollingMax_postcond (numbers : Array Int) (result : Array Int) (h_precond : rollingMax_precond numbers) : Prop :=
  result.size = numbers.size ∧ 
  (∀ i, i < numbers.size → result[i]! = seq_max (numbers.toList.take (i + 1)))

theorem rollingMax_spec_satisfied (numbers : Array Int) (h_precond : rollingMax_precond numbers) :
    rollingMax_postcond numbers (rollingMax numbers h_precond) h_precond := by
  sorry
-- </vc-theorems>