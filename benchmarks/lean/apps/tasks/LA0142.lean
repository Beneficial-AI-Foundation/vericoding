-- <vc-preamble>
def digit_sum : Nat → Nat
  | n => if n < 10 then n else (n % 10) + digit_sum (n / 10)

def int_to_string (n : Int) : String := toString n

@[reducible, simp]
def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  ∃ k : Int, k ≥ 1 ∧ k ≤ 10000 ∧ stdin_input = int_to_string k ++ "\n"

def kth_perfect_number (k : Int) : Int :=
  if k = 1 then 19
  else if k = 2 then 28
  else if k = 3 then 37
  else if k = 4 then 46
  else if k = 5 then 55
  else if k = 6 then 64
  else if k = 7 then 73
  else if k = 8 then 82
  else if k = 9 then 91
  else if k = 10 then 109
  else 10 * (k - 9) + 99

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
  (∃ k : Int, k ≥ 1 ∧ k ≤ 10000 ∧ 
      stdin_input = int_to_string k ++ "\n" ∧
      result = int_to_string (kth_perfect_number k) ++ "\n") ∧
  result.length > 0

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>