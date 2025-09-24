-- <vc-preamble>
def ValidInput (n : Int) (s : List Char) : Prop :=
  n ≥ 0 ∧ s.length = n.natAbs ∧ ∀ i, i < s.length → s[i]! = 'U' ∨ s[i]! = 'R'

def CountTransitionsHelper (s : List Char) (pos : Nat) (x : Int) (y : Int) (pred : Int) : Int :=
  if pos ≥ s.length then 0
  else
    let char := s[pos]!
    let newX := if char = 'U' then x else x + 1
    let newY := if char = 'U' then y + 1 else y
    if newX = newY then
      CountTransitionsHelper s (pos + 1) newX newY pred
    else
      let cur := if newX > newY then 0 else 1
      let transition := if cur ≠ pred ∧ pred ≠ -1 then 1 else 0
      transition + CountTransitionsHelper s (pos + 1) newX newY cur
termination_by s.length - pos

def CountKingdomTransitions (s : List Char) : Int :=
  if s.length = 0 then 0
  else CountTransitionsHelper s 0 0 0 (-1)

@[reducible, simp]
def solve_precond (n : Int) (s : List Char) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : List Char) (h_precond : solve_precond n s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : List Char) (result : Int) (h_precond : solve_precond n s) : Prop :=
  result ≥ 0 ∧ result ≤ n ∧ (n = 0 → result = 0) ∧ result = CountKingdomTransitions s

theorem solve_spec_satisfied (n : Int) (s : List Char) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>