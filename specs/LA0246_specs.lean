-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  ∀ i, i < s.length → s.data[i]! = 'L' ∨ s.data[i]! = 'R' ∨ s.data[i]! = 'U' ∨ s.data[i]! = 'D'

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def countCharHelper (s : String) (c : Char) (index : Nat) (count : Int) : Int :=
  if index ≥ s.length then count
  else if s.data[index]! = c then countCharHelper s c (index + 1) (count + 1)
  else countCharHelper s c (index + 1) count
termination_by s.length - index

def countChar (s : String) (c : Char) : Int :=
  countCharHelper s c 0 0

def countCharFromIndex (s : String) (c : Char) (index : Nat) : Int :=
  if index ≥ s.length then 0
  else if s.data[index]! = c then 1 + countCharFromIndex s c (index + 1)
  else countCharFromIndex s c (index + 1)
termination_by s.length - index

def CorrectResult (s : String) (result : Int) : Prop :=
  (s.length % 2 ≠ 0 → result = -1) ∧
  (s.length % 2 = 0 → result ≥ 0) ∧
  (s.length % 2 = 0 → result ≤ s.length / 2) ∧
  (s.length % 2 = 0 → result = (abs (countChar s 'L' - countChar s 'R') + abs (countChar s 'U' - countChar s 'D')) / 2)

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
  CorrectResult s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>