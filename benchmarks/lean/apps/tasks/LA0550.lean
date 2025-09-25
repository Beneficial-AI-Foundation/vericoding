-- <vc-preamble>

def ValidInput (s : String) : Prop :=
  s.length = 19 ∧ 
  s.length ≥ 2 ∧ 
  (if h : 5 < s.length then s.data[5]! = ',' else True) ∧ 
  (if h : 13 < s.length then s.data[13]! = ',' else True) ∧
  ∀ i, 0 ≤ i ∧ i < s.length → 
    (s.data[i]! = ',' ∨ ('a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'))

def CommasToSpaces (s : String) (h : ValidInput s) : String :=
  String.mk ((List.range s.length).map (fun i => 
    if i < s.length then
      if s.data[i]! = ',' then ' ' else s.data[i]!
    else ' '))

def CorrectOutput (s : String) (result : String) (h : ValidInput s) : Prop :=
  result.length = s.length + 1 ∧
  (if result.length > 0 then result.data[result.length - 1]! = '\n' else True) ∧
  ∀ i, 0 ≤ i ∧ i < s.length → 
    (s.data[i]! = ',' → result.data[i]! = ' ') ∧
    (s.data[i]! ≠ ',' → result.data[i]! = s.data[i]!)

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
  CorrectOutput s result h_precond

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>