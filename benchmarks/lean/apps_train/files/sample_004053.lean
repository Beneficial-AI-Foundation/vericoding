/-
Round any given number to the closest 0.5 step

I.E.
```
solution(4.2) = 4
solution(4.3) = 4.5
solution(4.6) = 4.5
solution(4.8) = 5
```

Round **up** if number is as close to previous and next 0.5 steps.

```
solution(4.75) == 5
```
-/

def solution (x : Float) : Float := sorry

def floor (x : Float) : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

def ceil (x : Float) : Float := sorry

theorem solution_output_options (x : Float) :
  let floorX := floor x
  solution x = floorX ∨ solution x = floorX + 0.5 ∨ solution x = ceil x
  := sorry

theorem solution_within_half (x : Float) :
  (solution x - x) ≤ 0.5 ∧ (x - solution x) ≤ 0.5
  := sorry

theorem solution_cases (x : Float) :
  let floorX := floor x
  (x - floorX < 0.25 → solution x = floorX) ∧ 
  (x - floorX < 0.75 ∧ x - floorX ≥ 0.25 → solution x = floorX + 0.5) ∧
  (x - floorX ≥ 0.75 → solution x = ceil x)
  := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solution 4.2

/-
info: 4.5
-/
-- #guard_msgs in
-- #eval solution 4.6

/-
info: 5
-/
-- #guard_msgs in
-- #eval solution 4.75

-- Apps difficulty: introductory
-- Assurance level: unguarded