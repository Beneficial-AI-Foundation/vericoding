/-
Your job is to return the volume of a cup when given the diameter of the top, the diameter of the bottom and the height.

You know that there is a steady gradient from the top to the bottom.

You want to return the volume rounded to 2 decimal places.

Exmples:
```python
cup_volume(1, 1, 1)==0.79

cup_volume(10, 8, 10)==638.79

cup_volume(1000, 1000, 1000)==785398163.4

cup_volume(13.123, 123.12, 1)==4436.57

cup_volume(5, 12, 31)==1858.51
```

You will only be passed positive numbers.
-/

-- <vc-helpers>
-- </vc-helpers>

def pi : Float := 3.14159

def cup_volume (d1 d2 h : Float) : Float := sorry

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

/-
info: 0.79
-/
-- #guard_msgs in
-- #eval cup_volume 1 1 1

/-
info: 638.79
-/
-- #guard_msgs in
-- #eval cup_volume 10 8 10

/-
info: 1858.51
-/
-- #guard_msgs in
-- #eval cup_volume 5 12 31

-- Apps difficulty: introductory
-- Assurance level: unguarded