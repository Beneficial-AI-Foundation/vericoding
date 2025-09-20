-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hello_world : String := sorry

theorem hello_world_consistency :
  hello_world = hello_world := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hello_world_is_string (s : String := hello_world) : 
  s = hello_world := by sorry

theorem hello_world_non_empty :
  hello_world.length > 0 := by sorry
-- </vc-theorems>