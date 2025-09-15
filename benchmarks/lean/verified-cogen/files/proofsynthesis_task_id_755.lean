-- <vc-preamble>
/- Helper spec function to find minimum value in a sequence -/
def minSpec (seq : List Int) : Int :=
  if h : seq.length = 1 then
    seq[0]!
  else if seq.length = 0 then
    0
  else
    let laterMin := minSpec (seq.tail)
    if seq[0]! ≤ laterMin then
      seq[0]!
    else
      laterMin
termination_by seq.length

@[reducible, simp]
def secondSmallest_precond (numbers : Array Int) :=
  numbers.size ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()