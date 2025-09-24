-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length ≥ 1 ∧ ∀ i, 0 ≤ i ∧ i < input.length → input.data.get! i = 'M' ∨ input.data.get! i = 'F'

def reverse (s : String) : String := 
  String.mk s.data.reverse

def find_char (s : String) (c : Char) (start : Nat) : Int :=
  let chars := s.data
  let rec helper (lst : List Char) (idx : Nat) : Int :=
    match lst with
    | [] => -1
    | h :: t => if h = c ∧ idx ≥ start then Int.ofNat idx else helper t (idx + 1)
  helper chars 0

def rfind_char (s : String) (c : Char) : Int :=
  let chars := s.data
  let rec helper (lst : List Char) (idx : Nat) (lastFound : Int) : Int :=
    match lst with
    | [] => lastFound
    | h :: t => if h = c then helper t (idx + 1) (Int.ofNat idx) else helper t (idx + 1) lastFound
  helper chars 0 (-1)

def calculate_balance (s : String) : Nat :=
  let chars := s.data
  let rec helper (lst : List Char) (balance : Nat) : Nat :=
    match lst with
    | [] => balance
    | h :: t => 
      if h = 'M' then helper t (balance + 1)
      else if h = 'F' ∧ balance > 0 then helper t (balance - 1)
      else helper t balance
  helper chars 0

def count_char (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

def substring (s : String) (start_idx end_idx : Int) : String :=
  if start_idx ≥ 0 ∧ end_idx ≥ start_idx ∧ end_idx ≤ s.length then
    let start_nat := Int.natAbs start_idx
    let end_nat := Int.natAbs end_idx
    if start_nat < s.data.length ∧ end_nat ≤ s.data.length then
      String.mk (s.data.drop start_nat |>.take (end_nat - start_nat))
    else ""
  else ""

def ComputeSwapTime (input : String) : Nat :=
  let rev_input := reverse input
  let first_f := find_char rev_input 'F' 0
  if first_f = -1 then 0
  else
    let first_m_after_f := find_char rev_input 'M' (Int.natAbs (first_f + 1))
    if first_m_after_f = -1 then 0
    else
      let last_m := rfind_char rev_input 'M'
      if last_m < first_m_after_f then 0
      else
        let sub := substring rev_input first_m_after_f (last_m + 1)
        let balance := calculate_balance sub
        let f_count := count_char sub 'F'
        Int.natAbs (balance + f_count + first_m_after_f - first_f - 1)

def nat_to_string (n : Nat) : String := toString n

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  result.length ≥ 1 ∧
  (if h : result.length > 0 then result.data.get! (result.length - 1) = '\n' else True) ∧
  (∃ val, val ≥ 0 ∧ result = nat_to_string val ++ "\n") ∧
  result = nat_to_string (ComputeSwapTime input) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>