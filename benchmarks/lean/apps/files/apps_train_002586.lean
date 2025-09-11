-- <vc-preamble>
def add (xs : List Int) : Int := sorry

structure WeightedSum where
  index : Nat 
  value : Int
  deriving Repr
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def makeWeightedSum (xs : List Int) : Int := match xs with
  | [] => 0
  | x::xs => x + makeWeightedSum xs
-- </vc-definitions>

-- <vc-theorems>
theorem add_weighted_sum (xs : List Int) (h : xs ≠ []) : 
  ∃ n, add xs = n := sorry

theorem add_single_number (x : Int) : 
  add [x] = x := sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded