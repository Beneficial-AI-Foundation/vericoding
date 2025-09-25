-- <vc-preamble>

def ValidInput (A B C K : Int) : Bool :=
  A ≥ 0 && B ≥ 0 && C ≥ 0 && K ≥ 1 && K ≤ A + B + C

def MaxSum (A B C K : Int) : Int :=
  if ValidInput A B C K then
    if K ≤ A + B then
      if K ≤ A then K else A
    else
      A - (K - A - B)
  else 0

def IntToStringPureHelper (n : Nat) : String := 
  if n < 10 then 
    String.singleton (Char.ofNat (48 + n))
  else 
    IntToStringPureHelper (n / 10) ++ String.singleton (Char.ofNat (48 + (n % 10)))
termination_by n

def IntToStringPure (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringPureHelper n.natAbs
  else IntToStringPureHelper n.natAbs

def SplitStringHelper (s : String) (i : Nat) (current : String) (parts : List String) : List String :=
  if i ≥ s.length then
    if current.length > 0 then parts ++ [current] else parts
  else 
    let c := s.data[i]!
    if c = ' ' ∨ c = '\n' then
      if current.length > 0 then 
        SplitStringHelper s (i+1) "" (parts ++ [current])
      else 
        SplitStringHelper s (i+1) "" parts
    else
      SplitStringHelper s (i+1) (current ++ String.singleton c) parts
termination_by s.length - i

def SplitStringPure (s : String) : List String :=
  if s.length = 0 then []
  else SplitStringHelper s 0 "" []

def StringToIntHelper (s : String) (start : Nat) : Int :=
  if start ≥ s.length then 0
  else 
    let c := s.data[start]!
    if '0' ≤ c ∧ c ≤ '9' then
      (c.toNat - '0'.toNat : Int) + 10 * StringToIntHelper s (start + 1)
    else
      StringToIntHelper s (start + 1)
termination_by s.length - start

def StringToIntPure (s : String) : Int :=
  if s.length = 0 then 0
  else if s.data[0]! = '-' then -StringToIntHelper s 1
  else StringToIntHelper s 0

def ParsedValues (input : String) (A B C K : Int) : Prop :=
  ∃ parts, parts.length ≥ 4 ∧
    parts = SplitStringPure input ∧
    A = StringToIntPure (parts[0]!) ∧
    B = StringToIntPure (parts[1]!) ∧
    C = StringToIntPure (parts[2]!) ∧
    K = StringToIntPure (parts[3]!) ∧
    ValidInput A B C K

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
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
  result.length > 0 ∧
  result.data[result.length - 1]! = '\n' ∧
  ((∃ A B C K, 
      ParsedValues input A B C K ∧
      (let maxSum := MaxSum A B C K;
       maxSum ≥ -2000000000 ∧ maxSum ≤ 2000000000 ∧
       result = IntToStringPure maxSum ++ "\n")) ∨
   (∀ A B C K, ¬ParsedValues input A B C K → result = "0\n"))

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>