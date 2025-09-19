-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trafficJam (road: String) (sides: List String) : String := sorry 

theorem trafficJam_endsWith_X (road: String) (sides: List String) 
  (h1: ∃ i, road.get i = 'X') :
  ∃ j, (trafficJam road sides).get j = 'X' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trafficJam_result_length 
  (road: String) (sides: List String) 
  (h1: ∃ i, road.get i = 'X')
  (h2: road.length > 0) :
  (trafficJam road sides).length ≥ road.length := sorry

theorem trafficJam_preserve_first_char
  (road: String) (sides: List String)
  (h1: sides.length > 0)
  (h2: sides[0] = "") 
  (h3: road.length > 0) :
  (trafficJam road sides).front = road.front := sorry

theorem trafficJam_minimal_case :
  trafficJam "X" [] = "X" := sorry

theorem trafficJam_single_char
  (road: String) (sides: List String)
  (h1: road.length = 2)
  (h2: road.back = 'X')
  (h3: sides = [""]) :
  (trafficJam road sides).length ≥ 2 ∧
  ∃ i, (trafficJam road sides).get i = 'X' := sorry
-- </vc-theorems>