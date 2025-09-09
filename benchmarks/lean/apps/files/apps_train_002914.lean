-- <vc-helpers>
-- </vc-helpers>

def get_volume_of_cuboid (length width height : Float) : Float := sorry

theorem volume_is_product {length width height : Float} 
  (h1 : length > 0) (h2 : width > 0) (h3 : height > 0) :
  let volume := get_volume_of_cuboid length width height 
  volume > 0 ∧ volume = length * width * height := sorry

theorem volume_respects_scaling {length width height scale : Float}
  (h1 : length > 0) (h2 : width > 0) (h3 : height > 0) (h4 : scale = 2):
  get_volume_of_cuboid (scale * length) (scale * width) (scale * height) = 
  get_volume_of_cuboid length width height * (scale * scale * scale) := sorry

/-
info: 60
-/
-- #guard_msgs in
-- #eval get_volume_of_cuboid 2 5 6

/-
info: 94.5
-/
-- #guard_msgs in
-- #eval get_volume_of_cuboid 6.3 3 5

-- Apps difficulty: introductory
-- Assurance level: unguarded