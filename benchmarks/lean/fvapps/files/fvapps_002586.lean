-- <vc-preamble>
structure WeightedSum where
  index : Nat
  value : Int
  deriving Repr

def makeWeightedSum (xs : List Int) : Int := match xs with
  | [] => 0
  | x::xs => x + makeWeightedSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add (xs : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_weighted_sum (xs : List Int) (h : xs ≠ []) :
  ∃ n, add xs = n :=
sorry

theorem add_single_number (x : Int) :
  add [x] = x :=
sorry
-- </vc-theorems>