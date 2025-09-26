import Mathlib
-- <vc-preamble>
def ParseNumbers (s : String) (i : Nat) (nums : List Int) (current : Int) (inNumber : Bool) : List Int :=
  if i ≥ s.length then
    if inNumber ∧ nums.length < 3 then nums ++ [current] else nums
  else if nums.length ≥ 3 then
    nums
  else
    let c := s.data[i]!
    if c ≥ '0' ∧ c ≤ '9' then
      let digit : Int := (c.toNat - '0'.toNat : Nat)
      if ¬inNumber then
        ParseNumbers s (i + 1) nums digit true
      else
        ParseNumbers s (i + 1) nums (current * 10 + digit) true
    else if inNumber then
      ParseNumbers s (i + 1) (nums ++ [current]) 0 false
    else
      ParseNumbers s (i + 1) nums current false
  termination_by s.length - i

def ParseThreeIntsFunc (s : String) : Int × Int × Int :=
  if s.length > 0 then
    let nums := ParseNumbers s 0 [] 0 false
    if nums.length ≥ 3 then 
      (nums[0]!, if nums[1]! > 0 then nums[1]! else 1, nums[2]!)
    else (0, 1, 0)
  else (0, 1, 0)

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 
  let parts := ParseThreeIntsFunc input
  parts.2.1 > 0

def IntToStringHelperFunc (n : Nat) : String :=
  if n < 10 then
    String.mk [Char.ofNat ('0'.toNat + n)]
  else
    IntToStringHelperFunc (n / 10) ++ String.mk [Char.ofNat ('0'.toNat + (n % 10))]
  termination_by n

def IntToStringFunc (n : Int) : String :=
  if n = 0 then "0"
  else if n < 0 then "-" ++ IntToStringHelperFunc n.natAbs
  else IntToStringHelperFunc n.natAbs

def ComputeMaxValue (a : Int) (b : Int) (n : Int) : Int :=
  if b > 0 then
    let minVal := if b - 1 < n then b - 1 else n
    (a * minVal) / b
  else 0

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma b_pos_of_precond (input : String) (h : solve_precond input) :
    (ParseThreeIntsFunc input).2.1 > 0 := by
  -- From precondition, we know ValidInput input
  have hv : ValidInput input := h.2
  -- Unfold ValidInput to extract the positivity of b
  dsimp [ValidInput] at hv
  exact hv.2
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let parts := ParseThreeIntsFunc input
  let a := parts.1
  let b := parts.2.1
  let n := parts.2.2
  IntToStringFunc (ComputeMaxValue a b n) ++ "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  let parts := ParseThreeIntsFunc input
  let a := parts.1
  let b := parts.2.1  
  let n := parts.2.2
  b > 0 ∧
  result = IntToStringFunc (ComputeMaxValue a b n) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  dsimp [solve_postcond, solve]
  constructor
  · have hv : ValidInput input := h_precond.2
    dsimp [ValidInput] at hv
    simpa using hv.2
  · rfl
-- </vc-theorems>
