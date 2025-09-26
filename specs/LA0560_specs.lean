-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∃ i, 0 ≤ i ∧ i < s.length ∧ '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def IsCelebratedAge (age : Int) : Prop :=
  age = 3 ∨ age = 5 ∨ age = 7

def ParseIntegerHelper (s : String) (pos : Nat) : Int :=
  if pos < s.length then
    let c := s.data[pos]!
    if '0' ≤ c ∧ c ≤ '9' then
      (c.toNat - '0'.toNat : Int)
    else
      0
  else
    0

def ParseIntegerValue (s : String) : Int :=
  if s.length > 0 then
    ParseIntegerHelper s 0
  else
    0

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
  let n := ParseIntegerValue stdin_input
  (IsCelebratedAge n → result = "YES\n") ∧
  (¬IsCelebratedAge n → result = "NO\n") ∧
  (result = "YES\n" ∨ result = "NO\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>