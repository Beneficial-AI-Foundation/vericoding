-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.get (String.Pos.mk i) = 'x' ∨ s.get (String.Pos.mk i) = 'y'

def countChar (s : String) (c : Char) : Nat :=
  (s.toList.filter (· = c)).length

def ValidOutput (s : String) (result : String) : Prop :=
  let countX := countChar s 'x'
  let countY := countChar s 'y'
  if countY > countX then
    result.length = countY - countX ∧ ∀ i, 0 ≤ i ∧ i < result.length → result.get (String.Pos.mk i) = 'y'
  else
    result.length = countX - countY ∧ ∀ i, 0 ≤ i ∧ i < result.length → result.get (String.Pos.mk i) = 'x'

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  ValidOutput s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>