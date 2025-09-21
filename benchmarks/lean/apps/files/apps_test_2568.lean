-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = '+' ∨ s.data[i]! = '-'

def computeResultHelper (s : String) (i : Nat) (cur : Int) (pm : Int) (ans : Int) : Int :=
  if h : i < s.length then
    if s.data[i]! = '+' then
      computeResultHelper s (i + 1) (cur + 1) pm ans
    else
      let newCur := cur - 1
      if newCur < pm then
        computeResultHelper s (i + 1) newCur newCur (ans + Int.ofNat i + 1)
      else
        computeResultHelper s (i + 1) newCur pm ans
  else ans
termination_by s.length - i

def computeResult (s : String) : Int :=
  computeResultHelper s 0 0 0 (Int.ofNat s.length)

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : Int) (h_precond : solve_precond s) : Prop :=
  result ≥ Int.ofNat s.length ∧ result = computeResult s

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>