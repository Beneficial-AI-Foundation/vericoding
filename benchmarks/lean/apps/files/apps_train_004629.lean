-- <vc-helpers>
-- </vc-helpers>

def calculate_ratio (width height : Nat) : String := sorry

theorem ratio_preservation 
  (width height : Nat) (h1 : width > 0) (h2 : height > 0) :
  let result := calculate_ratio width height
  let parts := result.split (· = ':')
  (String.toNat! parts[0]!) / (String.toNat! parts[1]!) = width / height := sorry

theorem zero_width_error (height : Nat) (h : height > 0) :
  calculate_ratio 0 height = "" := sorry

theorem zero_height_error (width : Nat) (h : width > 0) :
  calculate_ratio width 0 = "" := sorry

theorem common_ratio_sixteen_nine :
  calculate_ratio 16 9 = "16:9" := sorry

theorem common_ratio_four_three :
  calculate_ratio 4 3 = "4:3" := sorry

theorem common_ratio_one_one :
  calculate_ratio 1 1 = "1:1" := sorry

/-
info: '16:9'
-/
-- #guard_msgs in
-- #eval calculate_ratio 1920 1080

/-
info: '4:3'
-/
-- #guard_msgs in
-- #eval calculate_ratio 800 600

-- Apps difficulty: introductory
-- Assurance level: unguarded