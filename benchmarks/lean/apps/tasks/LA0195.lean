-- <vc-preamble>
def NumberToDigitsHelper (n : Nat) (acc : List Int) : List Int :=
  if n = 0 then acc
  else NumberToDigitsHelper (n / 10) ((n % 10 : Int) :: acc)
termination_by n

def NumberToDigits (n : Int) : List Int :=
  if n = 0 then [0]
  else if n > 0 then NumberToDigitsHelper n.natAbs []
  else NumberToDigitsHelper n.natAbs []

def AllDistinct (digits : List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < digits.length → digits[i]! ≠ digits[j]!

def HasDistinctDigits (n : Int) : Prop :=
  let digits := NumberToDigits n
  AllDistinct digits

def ValidInput (y : Int) : Prop :=
  1000 ≤ y ∧ y ≤ 9000

@[reducible, simp]
def solve_precond (y : Int) : Prop :=
  ValidInput y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (y : Int) (h_precond : solve_precond y) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (y : Int) (result : Int) (h_precond : solve_precond y) : Prop :=
  result > y ∧ HasDistinctDigits result ∧ (∀ n, y < n ∧ n < result → ¬HasDistinctDigits n)

theorem solve_spec_satisfied (y : Int) (h_precond : solve_precond y) :
    solve_postcond y (solve y h_precond) h_precond := by
  sorry
-- </vc-theorems>