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
/--
A helper function that returns one of two values based on the parity of a natural number.
- `even_case`: The value to return if `n` is even.
- `odd_case`: The value to return if `n` is odd.
-/
def Nat.parityBranch {α : Type} (n : Nat) (even_case : α) (odd_case : α) : α :=
  if n % 2 = 0 then even_case else odd_case

-- LLM HELPER
/-- If a number `n` is even, `Nat.parityBranch` returns the `even_case`. -/
theorem Nat.parityBranch_even {α : Type} (n : Nat) (h_even : n % 2 = 0) (even_case odd_case : α) :
  Nat.parityBranch n even_case odd_case = even_case := by
  simp [Nat.parityBranch, h_even]

-- LLM HELPER
/-- If a number `n` is odd, `Nat.parityBranch` returns the `odd_case`. -/
theorem Nat.parityBranch_odd {α : Type} (n : Nat) (h_odd : n % 2 = 1) (even_case odd_case : α) :
  Nat.parityBranch n even_case odd_case = odd_case := by
  have h_not_even : n % 2 ≠ 0 := by
    rw [h_odd]
    simp -- Proves 1 ≠ 0
  simp [Nat.parityBranch, h_not_even]
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  let username := input.take (input.length - 1)
  let distinctCount := CountDistinct username
  Nat.parityBranch distinctCount "CHAT WITH HER!\n" "IGNORE HIM!\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  let username := input.take (input.length - 1)
  CorrectOutput username output

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve_postcond, solve, CorrectOutput]
  constructor
  · intro h_odd
    rw [Nat.parityBranch_odd _ h_odd]
  · intro h_even
    rw [Nat.parityBranch_even _ h_even]
-- </vc-theorems>
