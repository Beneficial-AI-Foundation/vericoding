-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spider_to_fly (spider fly : WebCoord) : Float := sorry

def number_to_float (n : WebNumber) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem distance_nonnegative (spider fly : WebCoord) :
  spider_to_fly spider fly ≥ 0 := sorry

theorem distance_symmetric (spider fly : WebCoord) :
  spider_to_fly spider fly = spider_to_fly fly spider := sorry

theorem distance_self (coord : WebCoord) :
  spider_to_fly coord coord = 0 := sorry

theorem triangle_inequality (spider mid fly : WebCoord) :
  spider_to_fly spider fly ≤ spider_to_fly spider mid + spider_to_fly mid fly := sorry

theorem distance_to_origin (coord : WebCoord) :
  spider_to_fly coord ⟨WebLetter.A, WebNumber.N0⟩ = number_to_float coord.number := sorry

theorem same_radial_distance (coord : WebCoord) :
  spider_to_fly coord ⟨coord.letter, WebNumber.N0⟩ = number_to_float coord.number := sorry
-- </vc-theorems>