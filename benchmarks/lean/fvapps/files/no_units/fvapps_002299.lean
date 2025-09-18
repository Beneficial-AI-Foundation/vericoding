-- <vc-preamble>
def third_max (nums : List Int) : Int := sorry

def max (nums : List Int) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueSorted (nums : List Int) : List Int := sorry

theorem third_max_is_in_list {nums : List Int} (h : nums ≠ []) :
  third_max nums ∈ nums := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>