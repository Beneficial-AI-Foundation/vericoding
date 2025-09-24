-- <vc-preamble>
partial def isPowerOfTwo (n : Nat) : Bool :=
  if n == 0 then false
  else n == 1 || (n % 2 == 0 && isPowerOfTwo (n / 2))

partial def isLimitedPrimeHelper (p : Nat) (divisor : Nat) : Bool :=
  if divisor * divisor > p then true
  else if p % divisor == 0 then false
  else isLimitedPrimeHelper p (divisor + 2)

def isLimitedPrime (p : Nat) : Bool :=
  if p <= 1 then false
  else if p == 2 then true
  else if p % 2 == 0 then false
  else isLimitedPrimeHelper p 3

def determineWinner (n : Nat) : String :=
  if n == 1 then "FastestFinger"
  else if n == 2 then "Ashishgup"
  else if isPowerOfTwo n then "FastestFinger"
  else if n % 4 ≠ 2 then "Ashishgup"
  else if isLimitedPrime (n / 2) then "FastestFinger"
  else "Ashishgup"

@[reducible, simp]
def solve_precond (input : List Nat) : Prop :=
  input.length ≥ 1 ∧
  input[0]! ≥ 1 ∧
  input.length = input[0]! + 1 ∧
  ∀ i, 1 ≤ i ∧ i < input.length → input[i]! ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : List Nat) (h_precond : solve_precond input) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : List Nat) (result : List String) (h_precond : solve_precond input) : Prop :=
  result.length = input[0]! ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! = "FastestFinger" ∨ result[i]! = "Ashishgup") ∧
  (∀ i, 1 ≤ i ∧ i < input.length → result[i-1]! = determineWinner input[i]!)

theorem solve_spec_satisfied (input : List Nat) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>