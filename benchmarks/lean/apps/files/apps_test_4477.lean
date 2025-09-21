-- <vc-preamble>
def IsBoringApartment (x : Int) : Prop :=
  (x ≥ 1 ∧ x ≤ 9) ∨
  (x ≥ 11 ∧ x ≤ 99 ∧ x % 11 = 0 ∧ x / 11 ≥ 1 ∧ x / 11 ≤ 9) ∨
  (x ≥ 111 ∧ x ≤ 999 ∧ x % 111 = 0 ∧ x / 111 ≥ 1 ∧ x / 111 ≤ 9) ∨
  (x ≥ 1111 ∧ x ≤ 9999 ∧ x % 1111 = 0 ∧ x / 1111 ≥ 1 ∧ x / 1111 ≤ 9)

def DigitCount (n : Int) : Int :=
  if n ≤ 9 then 1
  else if n ≤ 99 then 2
  else if n ≤ 999 then 3
  else 4

def BoringApartmentValue (digit : Int) (length : Int) : Int :=
  if length = 1 then digit
  else if length = 2 then digit * 11
  else if length = 3 then digit * 111
  else digit * 1111

def TotalDigitsPressed (x : Int) : Int :=
  let digit := if x ≤ 9 then x 
               else if x ≤ 99 then x / 11
               else if x ≤ 999 then x / 111
               else x / 1111
  let length := DigitCount x
  let prevDigits := if digit = 1 then 0 else (digit - 1) * (1 + 2 + 3 + 4)
  let currentDigits := (length * (length + 1)) / 2
  prevDigits + currentDigits

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  IsBoringApartment x ∧ 1 ≤ x ∧ x ≤ 9999
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result : Int) (h_precond : solve_precond x) : Prop :=
  result ≥ 0 ∧ 
  result = TotalDigitsPressed x ∧
  (x = 1 → result = 1) ∧
  (x = 22 → result = 13) ∧
  (x = 777 → result = 66) ∧
  (x = 9999 → result = 90)

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  sorry
-- </vc-theorems>