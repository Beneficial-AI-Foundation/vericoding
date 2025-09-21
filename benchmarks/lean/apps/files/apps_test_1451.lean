-- <vc-preamble>

def ValidInput (n k : Int) (numbers : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 0 ∧ numbers.length = n ∧ ∀ i, 0 ≤ i ∧ i < numbers.length → numbers[i]! > 0

def countLuckyDigits (num : Int) : Int :=
  if h : num ≥ 0 then
    if num = 0 then 0
    else
      let digit := num % 10
      let rest := num / 10
      let digitCount := if digit = 4 ∨ digit = 7 then 1 else 0
      digitCount + countLuckyDigits rest
  else 0
termination_by num.natAbs

def countValidNumbers (numbers : List Int) (k : Int) (upTo : Nat) : Int :=
  if upTo = 0 then 0
  else
    let prevCount := countValidNumbers numbers k (upTo - 1)
    if h : upTo - 1 < numbers.length then
      if countLuckyDigits numbers[upTo - 1]! ≤ k then prevCount + 1 else prevCount
    else prevCount

@[reducible, simp]
def solve_precond (n k : Int) (numbers : List Int) : Prop :=
  ValidInput n k numbers
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (numbers : List Int) (h_precond : solve_precond n k numbers) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (numbers : List Int) (result : Int) (h_precond : solve_precond n k numbers) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result = (numbers.filter (fun num => countLuckyDigits num ≤ k)).length

theorem solve_spec_satisfied (n k : Int) (numbers : List Int) (h_precond : solve_precond n k numbers) :
    solve_postcond n k numbers (solve n k numbers h_precond) h_precond := by
  sorry
-- </vc-theorems>