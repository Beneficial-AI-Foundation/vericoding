-- <vc-preamble>
def maximum (xs: List Int) : Int := match xs with
  | [] => 0
  | h::t => t.foldl max h

def minimum (xs: List Int) : Int := match xs with
  | [] => 0
  | h::t => t.foldl min h
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestRangeII (nums: List Int) (k: Int) : Int := sorry

theorem result_nonnegative (nums: List Int) (k: Int) (h: k ≥ 0) :
  smallestRangeII nums k ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_gives_zero (x: Int) (k: Int) :
  smallestRangeII [x] k = 0 := sorry

theorem empty_list_gives_zero (k: Int) :
  smallestRangeII [] k = 0 := sorry
-- </vc-theorems>