-- <vc-preamble>
@[reducible, simp]
def intersperse_precond (numbers : Array Int) (delim : Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def intersperse (numbers : Array Int) (delim : Int) (h_precond : intersperse_precond numbers delim) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def intersperse_postcond (numbers : Array Int) (delim : Int) (res: Array Int) (h_precond : intersperse_precond numbers delim) : Prop :=
  (numbers.size = 0 → res.size = 0) ∧ 
  (numbers.size ≠ 0 → res.size = 2 * numbers.size - 1) ∧
  (∀ i, 0 ≤ i ∧ i < res.size ∧ i % 2 = 0 → res[i]! = numbers[i / 2]!) ∧
  (∀ i, 0 ≤ i ∧ i < res.size ∧ i % 2 = 1 → res[i]! = delim)

theorem intersperse_spec_satisfied (numbers: Array Int) (delim: Int) (h_precond : intersperse_precond numbers delim) :
    intersperse_postcond numbers delim (intersperse numbers delim h_precond) h_precond := by
  sorry
-- </vc-theorems>