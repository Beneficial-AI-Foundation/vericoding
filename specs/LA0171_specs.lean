-- <vc-preamble>
@[reducible, simp]
def ValidInput (s : String) : Prop :=
  s.length > 0

def FindFirstNewline (s : String) : Int :=
  let rec find_aux (chars : List Char) (pos : Nat) : Int :=
    match chars with
    | [] => -1
    | c :: rest => if c = '\n' then Int.ofNat pos else find_aux rest (pos + 1)
  find_aux s.toList 0

def ExtractFirstLine (s : String) : String :=
  let newline_pos := FindFirstNewline s
  if newline_pos = -1 then s 
  else 
    let pos_nat := Int.natAbs newline_pos
    s.take pos_nat

def ReverseString (s : String) : String :=
  String.mk (s.toList.reverse)

@[reducible, simp]
def ValidOutput (result : String) (input : String) : Prop :=
  result.length ≥ 1 ∧
  (result.length > 0 → result.back = '\n') ∧
  ∃ n : String, 
    n = ExtractFirstLine input ∧
    result = n ++ ReverseString n ++ "\n"

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  ValidOutput result stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>