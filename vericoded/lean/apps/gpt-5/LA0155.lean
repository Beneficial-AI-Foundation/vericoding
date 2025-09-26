import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length ≥ 1 ∧ s.length ≤ 20 ∧ ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def DistinctStringsCount (s : String) : Int :=
  s.length * 25 + 26

def char_of_digit (d : Int) : Char :=
  if d = 0 then '0'
  else if d = 1 then '1'
  else if d = 2 then '2'
  else if d = 3 then '3'
  else if d = 4 then '4'
  else if d = 5 then '5'
  else if d = 6 then '6'
  else if d = 7 then '7'
  else if d = 8 then '8'
  else '9'

def int_to_string_helper (n : Nat) (acc : String) : String :=
  if n = 0 then acc
  else 
    let digit := char_of_digit (n % 10)
    int_to_string_helper (n / 10) (String.mk [digit] ++ acc)

def int_to_string (n : Int) : String :=
  if n ≤ 0 then "0"
  else int_to_string_helper n.natAbs ""

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma int_to_string_nonpos {n : Int} (h : n ≤ 0) : int_to_string n = "0" := by
  unfold int_to_string
  simp [h]

-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  int_to_string (DistinctStringsCount s)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result: String) (h_precond : solve_precond s) : Prop :=
  result = int_to_string (DistinctStringsCount s)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
