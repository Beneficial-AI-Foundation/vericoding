-- <vc-preamble>
@[reducible, simp]
def append_precond (a : Array Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc
-- </vc-helpers>

-- <vc-definitions>
def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1

theorem append_spec_satisfied (a: Array Int) (b: Int) (h_precond : append_precond (a) (b)) :
    append_postcond (a) (b) (append (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>