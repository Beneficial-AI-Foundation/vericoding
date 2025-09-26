import Mathlib
-- <vc-preamble>

def int_to_string (_ : Int) : String :=
  "1"

def parse_int_from_string (_ : String) : Int :=
  1

def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0

def sum_of_non_fizzbuzz_numbers (n : Nat) : Int :=
  if n = 0 then 0
  else
    let num := Int.ofNat n
    if num % 3 > 0 ∧ num % 5 > 0 then
      sum_of_non_fizzbuzz_numbers (n - 1) + num
    else
      sum_of_non_fizzbuzz_numbers (n - 1)

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def parse_valid_nat (s : String) : Nat :=
  s.toNat?.getD 0

-- LLM HELPER
lemma int_to_string_nonempty (n : Int) : (int_to_string n).length > 0 := by
  unfold int_to_string
  decide
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  let n := parse_valid_nat stdin_input
  let result := sum_of_non_fizzbuzz_numbers n
  int_to_string result
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  result.length > 0

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond solve
  simp only [solve_precond] at h_precond
  apply int_to_string_nonempty
-- </vc-theorems>
