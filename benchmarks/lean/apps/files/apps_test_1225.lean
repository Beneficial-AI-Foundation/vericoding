-- <vc-preamble>
def ValidInput (h : Int) : Prop :=
  h ≥ 1

def pow2 (n : Nat) : Nat :=
  if n = 0 then 1 else 2 * pow2 (n - 1)

def ComputeAttacksIterative (h : Nat) (n : Nat) : Nat :=
  if h = 0 then 0 else pow2 n + ComputeAttacksIterative (h / 2) (n + 1)
termination_by h

def ComputeAttacks (h : Int) : Int :=
  if h ≤ 0 then 0 else Int.ofNat (ComputeAttacksIterative h.natAbs 0)

def ParseIntHelper (s : String) (i : Nat) (acc : Nat) : Nat :=
  if i ≥ s.length then acc
  else 
    let c := s.data[i]!
    if c = '\n' ∨ c = ' ' then acc
    else if '0' ≤ c ∧ c ≤ '9' then
      ParseIntHelper s (i + 1) (acc * 10 + c.toNat - '0'.toNat)
    else
      ParseIntHelper s (i + 1) acc
termination_by s.length - i

def ParseIntFunc (s : String) : Int :=
  Int.ofNat (ParseIntHelper s 0 0)

def IntToStringHelper (n : Nat) (acc : String) : String :=
  if n = 0 then acc
  else
    let digit := n % 10
    let digitChar := Char.ofNat ('0'.toNat + digit)
    IntToStringHelper (n / 10) (String.mk [digitChar] ++ acc)
termination_by n

def IntToStringFunc (n : Int) : String :=
  if n ≤ 0 then "0" else IntToStringHelper n.natAbs ""

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
def solve_postcond (stdin_input : String) (output : String) (h_precond : solve_precond stdin_input) : Prop :=
  output.length > 0 ∧ 
  (output.length > 0 → output.data[output.length - 1]! = '\n') ∧
  (let h := ParseIntFunc stdin_input;
   ValidInput h → output = IntToStringFunc (ComputeAttacks h) ++ "\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>