-- <vc-helpers>
-- </vc-helpers>

def Point := Prod Float Float

def calculate_triangle_area_sum : List Point → Float := sorry

theorem known_case_1 :
  let points := [(1.0,1.0), (2.0,1.0), (3.0,3.0)]
  Float.abs (calculate_triangle_area_sum points - 1.0) < 0.01 := sorry

theorem known_case_2 :
  let points := [(1.0,1.0), (2.0,2.0), (2.0,1.0), (3.0,3.0)]
  Float.abs (calculate_triangle_area_sum points - 2.0) < 0.01 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded