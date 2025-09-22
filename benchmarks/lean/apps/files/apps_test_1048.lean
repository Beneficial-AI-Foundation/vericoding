-- <vc-preamble>
def count_char (s : String) (c : Char) : Int :=
  s.toList.count c

def my_min (a b : Int) : Int :=
  if a ≤ b then a else b

def ValidCommands (commands : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < commands.length → True

@[reducible, simp]
def solve_precond (n : Int) (commands : String) : Prop :=
  n ≥ 0 ∧ commands.length = n ∧ ValidCommands commands
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (commands : String) (h_precond : solve_precond n commands) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (commands : String) (result : Int) (h_precond : solve_precond n commands) : Prop :=
  result ≥ 0 ∧ 
  result ≤ n ∧ 
  result % 2 = 0 ∧
  result = 2 * my_min (count_char commands 'L') (count_char commands 'R') + 
           2 * my_min (count_char commands 'U') (count_char commands 'D')

theorem solve_spec_satisfied (n : Int) (commands : String) (h_precond : solve_precond n commands) :
    solve_postcond n commands (solve n commands h_precond) h_precond := by
  sorry
-- </vc-theorems>