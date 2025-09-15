-- <vc-preamble>
/- Specification function for absolute value -/
def absSpec (i : Int) : Int :=
  if i < 0 then -i else i

/- Precondition for hasCloseElements function -/
@[reducible, simp]
def hasCloseElements_precond (numbers : Array Int) (threshold : Int) : Prop :=
  threshold > 0 ∧ 
  ∀ i j, 0 ≤ i ∧ i < numbers.size ∧ 0 ≤ j ∧ j < numbers.size → 
    numbers[i]! - numbers[j]! < 2147483647 ∧ -(numbers[i]! - numbers[j]!) < 2147483647
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()