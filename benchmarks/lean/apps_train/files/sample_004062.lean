/-
Given an array of 4 integers  
```[a,b,c,d]``` representing two points ```(a, b)``` and ```(c, d)```, return a string representation of the slope of the line joining these two points. 

For an undefined slope (division by 0), return  ```undefined```  . Note that the "undefined" is case-sensitive.
```
   a:x1
   b:y1
   c:x2
   d:y2
```

Assume that ```[a,b,c,d]``` and the answer are all integers 
(no floating numbers!).
Slope:
-/

-- <vc-helpers>
-- </vc-helpers>

def find_slope (points : List Int) : String :=
  sorry

theorem slope_undefined_when_x_equal {x1 y1 x2 y2 : Int} 
  (h : x1 = x2) :
  find_slope [x1, y1, x2, y2] = "undefined" :=
sorry

theorem slope_calculation_when_x_different {x1 y1 x2 y2 : Int}
  (h : x1 ≠ x2) 
  (bound1 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (bound2 : -1000 ≤ x2 ∧ x2 ≤ 1000)
  (bound3 : -1000 ≤ y1 ∧ y1 ≤ 1000)
  (bound4 : -1000 ≤ y2 ∧ y2 ≤ 1000) :
  find_slope [x1, y1, x2, y2] = toString ((y2 - y1) / (x2 - x1)) :=
sorry

theorem vertical_line_slope {x y1 : Int}
  (bound1 : -1000 ≤ x ∧ x ≤ 1000)
  (bound2 : -1000 ≤ y1 ∧ y1 ≤ 1000) :
  find_slope [x, y1, x, y1 + 10] = "undefined" :=
sorry

theorem horizontal_line_slope {x1 y : Int}
  (bound1 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (bound2 : -1000 ≤ y ∧ y ≤ 1000) :
  find_slope [x1, y, x1 + 10, y] = "0" :=
sorry

/-
info: '4'
-/
-- #guard_msgs in
-- #eval find_slope [3, 6, 4, 10]

/-
info: '0'
-/
-- #guard_msgs in
-- #eval find_slope [12, -18, -15, -18]

/-
info: 'undefined'
-/
-- #guard_msgs in
-- #eval find_slope [17, -3, 17, 8]

-- Apps difficulty: introductory
-- Assurance level: unguarded