-- <vc-preamble>
def ValidInput (a : List Int) : Prop :=
  a.length > 0

def isSorted (x : List Int) : Bool :=
  if x.length ≤ 1 then true
  else List.range (x.length - 1) |>.all fun i => x[i]! ≤ x[i + 1]!

def thanosSort (x : List Int) : Int :=
  if x.length = 0 then 1
  else if x.length = 1 then 1
  else
    let len := x.length
    if isSorted x then
      len
    else
      let firstHalf := x.take (len / 2)
      let secondHalf := x.drop (len / 2)
      let leftResult := thanosSort firstHalf
      let rightResult := thanosSort secondHalf
      if leftResult > rightResult then leftResult else rightResult
termination_by x.length

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  ValidInput a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : Int) (h_precond : solve_precond a) : Prop :=
  result = thanosSort a ∧ 1 ≤ result ∧ result ≤ a.length

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>