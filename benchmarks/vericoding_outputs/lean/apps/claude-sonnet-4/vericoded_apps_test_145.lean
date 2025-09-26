import Mathlib
-- <vc-preamble>
def CountDistinct (s : String) : Nat :=
  (s.toList.eraseDups).length

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (input.length > 0 → input.data[input.length - 1]! = '\n') ∧
  input.length ≥ 2 ∧
  ∀ i, 0 ≤ i ∧ i < input.length - 1 → 
    'a' ≤ input.data[i]! ∧ input.data[i]! ≤ 'z'

def CorrectOutput (username : String) (output : String) : Prop :=
  let distinctCount := CountDistinct username
  (distinctCount % 2 = 1 → output = "IGNORE HIM!\n") ∧
  (distinctCount % 2 = 0 → output = "CHAT WITH HER!\n")

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n

-- LLM HELPER  
lemma not_mod_two_eq_one_of_mod_two_eq_zero {n : Nat} (h : n % 2 = 0) : ¬(n % 2 = 1) := by
  rw [h]
  norm_num
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let username := input.take (input.length - 1)
  let distinctCount := CountDistinct username
  if distinctCount % 2 = 1 then "IGNORE HIM!\n" else "CHAT WITH HER!\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  let username := input.take (input.length - 1)
  CorrectOutput username output

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond CorrectOutput solve
  constructor
  · intro h_odd
    simp only [if_pos h_odd]
  · intro h_even
    have h_not_odd := not_mod_two_eq_one_of_mod_two_eq_zero h_even
    simp only [if_neg h_not_odd]
-- </vc-theorems>
