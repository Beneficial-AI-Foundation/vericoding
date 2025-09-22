-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  (s.length = 3 ∨ (s.length = 4 ∧ s.data[3]! = '\n')) ∧
  ∀ i, 0 ≤ i ∧ i < (if s.length = 4 then 3 else s.length) → 
    (s.data[i]! = 'a' ∨ s.data[i]! = 'b' ∨ s.data[i]! = 'c')

def GetInputChars (s : String) : String :=
  if s.length = 4 then s.take 3 else s

def IsPermutationOfABC (input_chars : String) : Prop :=
  input_chars.length = 3 ∧
  (∀ i, 0 ≤ i ∧ i < input_chars.length → 
    (input_chars.data[i]! = 'a' ∨ input_chars.data[i]! = 'b' ∨ input_chars.data[i]! = 'c')) ∧
  input_chars.data[0]! ≠ input_chars.data[1]! ∧ 
  input_chars.data[1]! ≠ input_chars.data[2]! ∧ 
  input_chars.data[0]! ≠ input_chars.data[2]!

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length ≥ 3 ∧ ValidInput s
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
  (result = "Yes\n" ∨ result = "No\n") ∧
  (result = "Yes\n" ↔ IsPermutationOfABC (GetInputChars s))

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>