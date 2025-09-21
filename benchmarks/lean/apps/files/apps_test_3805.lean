-- <vc-preamble>
def ExtractFirstLine (input : List Char) : List Char :=
  match input with
  | [] => []
  | c :: rest => 
    if c = '\n' then []
    else c :: ExtractFirstLine rest

def ProcessString (input : List Char) (stack : List Char) : List Char :=
  match input with
  | [] => stack
  | c :: rest =>
    let newStack := match stack with
      | [] => [c]
      | top :: stackRest => 
        if top = c then stackRest
        else c :: stack
    ProcessString rest newStack

def StackAlgorithmResultsInEmptyStack (input : List Char) : Prop :=
  let stack := ProcessString input []
  stack.length = 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (result = "Yes\n" ∨ result = "No\n") ∧ 
  (result = "Yes\n" ↔ StackAlgorithmResultsInEmptyStack (ExtractFirstLine input.toList))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>