-- <vc-preamble>
def ValidDNABase (c : Char) : Prop :=
  c = 'A' ∨ c = 'T' ∨ c = 'C' ∨ c = 'G'

instance : Decidable (ValidDNABase c) := by
  unfold ValidDNABase
  infer_instance

def DNAComplement (c : Char) : Char :=
  if c = 'A' then 'T'
  else if c = 'T' then 'A'
  else if c = 'C' then 'G'
  else 'G'

def find_newline (input : String) : Nat :=
  input.toList.findIdx (· = '\n')

def ValidInput (input : String) : Prop :=
  let input_line := if input.contains '\n'
                    then input.take (find_newline input)
                    else input
  input_line.length = 1 ∧ ValidDNABase (input_line.get! 0)

instance : Decidable (ValidInput input) := by
  unfold ValidInput
  infer_instance

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result: String) (h_precond : solve_precond stdin_input) : Prop :=
  let input_line := if stdin_input.contains '\n'
                    then stdin_input.take (find_newline stdin_input)
                    else stdin_input
  if ValidInput stdin_input then
    result = (String.mk [DNAComplement (input_line.get! 0)]) ++ "\n"
  else
    result = ""

theorem solve_spec_satisfied (stdin_input: String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>