-- <vc-helpers>
-- </vc-helpers>

def hello_world : String := sorry

theorem hello_world_consistency :
  hello_world = hello_world := by sorry

theorem hello_world_is_string (s : String := hello_world) : 
  s = hello_world := by sorry

theorem hello_world_non_empty :
  hello_world.length > 0 := by sorry

/-
info: 'Hello, World!'
-/
-- #guard_msgs in
-- #eval hello_world

-- Apps difficulty: introductory
-- Assurance level: unguarded