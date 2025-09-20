-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pi : Float := 3.14159

def cup_volume (d1 d2 h : Float) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cup_volume_positive
  (d1 d2 h : Float)
  (h1 : d1 > 1)
  (h2 : d2 > 1) 
  (h3 : h > 1) :
  cup_volume d1 d2 h > 0 := sorry

theorem cup_volume_scales_linearly
  (d1 d2 h scale : Float)
  (h1 : d1 > 1)
  (h2 : d2 > 1)
  (h3 : h > 1)
  (h4 : scale = 2) :
  cup_volume d1 d2 (h * scale) = cup_volume d1 d2 h * scale := sorry

theorem cup_volume_symmetric
  (d1 d2 h : Float)
  (h1 : d1 > 1)
  (h2 : d2 > 1)
  (h3 : h > 1) :
  cup_volume d1 d2 h = cup_volume d2 d1 h := sorry

theorem cup_volume_cylinder_case
  (d h : Float) 
  (h1 : d > 1)
  (h2 : h > 1) :
  cup_volume d d h = pi * (d * d) * h / 4 := sorry
-- </vc-theorems>