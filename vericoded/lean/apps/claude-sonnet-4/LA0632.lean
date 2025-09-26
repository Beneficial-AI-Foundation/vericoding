import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length = 3 ∧ ∀ i, 0 ≤ i ∧ i < s.length → s.data[i]! = 'o' ∨ s.data[i]! = 'x'

def countO (s : List Char) : Nat :=
  match s with
  | [] => 0
  | c :: cs => (if c = 'o' then 1 else 0) + countO cs

def countOString (s : String) : Nat :=
  countO s.data

def CalculatePrice (s : String) : Nat :=
  countOString s * 100 + 700

def IntToStringHelper (n : Nat) (acc : String) : String :=
  if n = 0 then acc
  else IntToStringHelper (n / 10) (String.mk [Char.ofNat (n % 10 + 48)] ++ acc)
termination_by n

def IntToString (n : Nat) : String :=
  if n = 0 then "0"
  else IntToStringHelper n ""

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma CalculatePrice_ge_700 (s : String) : CalculatePrice s ≥ 700 := by
  unfold CalculatePrice countOString
  exact Nat.le_add_left 700 (countO s.data * 100)
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  IntToString (CalculatePrice s) ++ "\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  result = IntToString (CalculatePrice s) ++ "\n" ∧ CalculatePrice s ≥ 700

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · rfl
  · exact CalculatePrice_ge_700 s
-- </vc-theorems>
