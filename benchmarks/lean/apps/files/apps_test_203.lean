-- <vc-preamble>
def ValidInput (n : Int) (s : String) : Prop :=
  1 ≤ n ∧ n ≤ 200000 ∧ s.length = n.natAbs ∧ 
  ∀ i, 0 ≤ i ∧ i < s.length → s.data.get! i = 'D' ∨ s.data.get! i = 'R'

def CountD (s : String) : Int :=
  s.data.foldl (fun acc c => if c = 'D' then acc + 1 else acc) 0

def CountR (s : String) : Int :=
  s.data.foldl (fun acc c => if c = 'R' then acc + 1 else acc) 0

def OptimalEliminationGameWinner (s : String) : String :=
  if CountD s = 0 then "R"
  else if CountR s = 0 then "D"
  else if CountD s ≥ CountR s then "D"
  else "R"

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : String) (h_precond : solve_precond n s) : Prop :=
  (result = "D" ∨ result = "R") ∧
  (result = "D" → CountD s > 0) ∧
  (result = "R" → CountR s > 0) ∧
  (CountD s = 0 → result = "R") ∧
  (CountR s = 0 → result = "D") ∧
  ((∀ i, 0 ≤ i ∧ i < s.length → s.data.get! i = 'D') → result = "D") ∧
  ((∀ i, 0 ≤ i ∧ i < s.length → s.data.get! i = 'R') → result = "R") ∧
  result = OptimalEliminationGameWinner s

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>