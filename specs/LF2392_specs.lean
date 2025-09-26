-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort (as : List Nat) : List Nat :=
sorry

def countMismatches (xs ys : List Nat) : Nat :=
sorry

def height_checker (heights : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem height_checker_singleton (x : Nat) :
  height_checker [x] = 0 :=
sorry

theorem height_checker_uniform (x n : Nat) :
  n > 0 →
  height_checker (List.replicate n x) = 0 :=
sorry
-- </vc-theorems>