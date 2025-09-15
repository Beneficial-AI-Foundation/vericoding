-- <vc-preamble>
/- Helper functions for recursively computing max and min of a list -/
def maxRcur (seq : List Int) : Int :=
  match seq with
  | [] => 0  /- Should not happen given preconditions -/
  | [x] => x
  | x :: xs => max x (maxRcur xs)

def minRcur (seq : List Int) : Int :=
  match seq with
  | [] => 0  /- Should not happen given preconditions -/
  | [x] => x  
  | x :: xs => min x (minRcur xs)

@[reducible, simp]
def sumMinMax_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ ∀ i, i < arr.size → -1073741824 < arr[i]! ∧ arr[i]! < 1073741823
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>
