/-
Americans are odd people: in their buildings, the first floor is actually the ground floor and there is no 13th floor (due to superstition).

Write a function that given a floor in the american system returns the floor in the european system.

With the 1st floor being replaced by the ground floor and the 13th floor being removed, the numbers move down to take their place. In case of above 13, they move down by two because there are two omitted numbers below them.

Basements (negatives) stay the same as the universal level.

[More information here](https://en.wikipedia.org/wiki/Storey#European_scheme)

## Examples

```
1  =>  0 
0  =>  0
5  =>  4
15  =>  13
-3  =>  -3
```
-/

-- <vc-helpers>
-- </vc-helpers>

def get_real_floor (n : Int) : Int := sorry

theorem negative_and_zero_floors_unchanged
  {floor : Int}
  (h : floor ≤ 0) :
  get_real_floor floor = floor := sorry

theorem floors_below_13_decreased_by_one
  {floor : Int}
  (h1 : floor > 0)
  (h2 : floor < 13) :
  get_real_floor floor = floor - 1 := sorry

theorem floors_above_12_decreased_by_two
  {floor : Int}
  (h : floor ≥ 13) :
  get_real_floor floor = floor - 2 := sorry

theorem floor_13_maps_to_11 :
  get_real_floor 13 = 11 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval get_real_floor 5

/-
info: 13
-/
-- #guard_msgs in
-- #eval get_real_floor 15

/-
info: -3
-/
-- #guard_msgs in
-- #eval get_real_floor -3

-- Apps difficulty: introductory
-- Assurance level: unguarded