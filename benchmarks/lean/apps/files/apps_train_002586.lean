def add (xs : List Int) : Int := sorry

structure WeightedSum where
  index : Nat 
  value : Int
  deriving Repr

-- <vc-helpers>
-- </vc-helpers>

def makeWeightedSum (xs : List Int) : Int := match xs with
  | [] => 0
  | x::xs => x + makeWeightedSum xs

theorem add_weighted_sum (xs : List Int) (h : xs ≠ []) : 
  ∃ n, add xs = n := sorry

theorem add_single_number (x : Int) : 
  add [x] = x := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded