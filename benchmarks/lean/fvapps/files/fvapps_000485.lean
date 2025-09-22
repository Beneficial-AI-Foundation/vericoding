-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_increment_for_unique (nums : List Int) : Nat :=
  sorry

def sorted (l : List Int) : List Int :=
  sorry

def makeUnique (nums : List Int) : List Int :=
  sorry

def sumList (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_increment_nonneg (nums : List Int) :
  min_increment_for_unique nums ≥ 0 :=
sorry

theorem min_increment_empty (nums : List Int) :
  nums = [] → min_increment_for_unique nums = 0 :=
sorry

theorem min_increment_single (nums : List Int) (x : Int) :
  nums = [x] → min_increment_for_unique nums = 0 :=
sorry

theorem min_increment_sort_invariant (nums : List Int) :
  min_increment_for_unique nums = min_increment_for_unique (sorted nums) :=
sorry

theorem min_increment_makes_unique (nums : List Int) :
  let result := sorted nums
  let incremented := makeUnique result
  min_increment_for_unique nums = (sumList incremented - sumList result) :=
sorry
-- </vc-theorems>