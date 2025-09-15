-- <vc-preamble>
def maxInt (a b : Int) : Int := if a ≥ b then a else b
def minInt (a b : Int) : Int := if a ≤ b then a else b

def maxRcur : List Int → Int
  | [] => 0
  | [x] => x
  | xs => maxInt xs.getLast! (maxRcur xs.dropLast)
termination_by xs => xs.length
decreasing_by
  simp_wf
  sorry

def minRcur : List Int → Int
  | [] => 0
  | [x] => x
  | xs => minInt xs.getLast! (minRcur xs.dropLast)
termination_by xs => xs.length
decreasing_by
  simp_wf
  sorry

@[reducible, simp]
def differenceMaxMin_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ (∀ i, i < arr.size → (-2147483648 / 2) < arr[i]! ∧ arr[i]! < (2147483647 / 2))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()