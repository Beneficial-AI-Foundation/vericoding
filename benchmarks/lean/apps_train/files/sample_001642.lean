/-
Spider-Man ("Spidey") needs to get across town for a date with Mary Jane and his web-shooter is low on web fluid. He travels by slinging his web rope to latch onto a building rooftop, allowing him to swing to the opposite end of the latch point.
Write a function that, when given a list of buildings, returns a list of optimal rooftop latch points for minimal web expenditure.
Input
Your function will receive an array whose elements are subarrays in the form [h,w] where h and w represent the height and width, respectively, of each building in sequence
Output
An array of latch points (integers) to get from 0 to the end of the last building in the input list
Technical Details

An optimal latch point is one that yields the greatest horizontal distance gain relative to length of web rope used. Specifically, the highest horizontal distance yield per length unit of web rope used. Give this value rounded down to the nearest integer as a distance from Spidey's origin point (0)
At the start of each swing, Spidey selects a latch point based on his current position.
At the end of each swing, Spidey ends up on the opposite side of the latch point equal to his distance from the latch point before swing.
Spidey's initial altitude is 50, and will always be the same at the start and end of each swing. His initial horizontal position is 0.
To avoid collision with people/traffic below, Spidey must maintain a minimum altitude of 20 at all times.
Building height (h) range limits: 125 <= h < 250
Building width (w) range limits: 50 <= w <= 100
Inputs will always be valid.

Test Example

- Spidey's initial position is at `0`. His first latch point is marked at `76` (horizontal position) on `buildings[0]`.
- At the end of the swing, Spidey's position is at the point marked `B` with a horizontal position of `152`. The green arc represents Spidey's path during swing.
- The marker on the 3rd building and the arc going from point `B` to point `C` represent the latch point (`258`) and arc path for the next swing.

```python
buildings = [[162,76], [205,96], [244,86], [212,68], [174,57], [180,89], [208,70], [214,82], [181,69], [203,67]]

spidey_swings(buildings)# [76,258,457,643,748]
-/

def spidey_swings (buildings : BuildingParams) : List Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_widths (buildings : BuildingParams) : Int :=
  List.foldl (fun acc b => acc + b.width) 0 buildings

@[simp] theorem spidey_swings_nonempty {buildings : BuildingParams} 
  (h : buildings ≠ []) : 
  (spidey_swings buildings).length > 0 :=
sorry

theorem spidey_swings_result_elements_increasing {buildings : BuildingParams}
  (h : buildings ≠ []) :
  ∀ i, i < (spidey_swings buildings).length - 1 → 
    (spidey_swings buildings)[i]! < (spidey_swings buildings)[i+1]! :=
sorry

theorem spidey_swings_within_bounds {buildings : BuildingParams}
  (h : buildings ≠ []) :
  let total_width := sum_widths buildings
  ∀ pos ∈ spidey_swings buildings, 0 ≤ pos ∧ pos ≤ total_width :=
sorry

theorem spidey_swings_min_height {buildings : BuildingParams}
  (h : buildings ≠ []) 
  (b : Building) (hb : b ∈ buildings) :
  b.height ≥ 50 :=
sorry

theorem spidey_swings_uniform_height_bound 
  {buildings : BuildingParams}
  (h₁ : buildings ≠ [])
  (h₂ : ∀ (b : Building), b ∈ buildings → b.height = 100)
  (h₃ : ∀ (b : Building), b ∈ buildings → 10 ≤ b.width ∧ b.width ≤ 20)
  (h₄ : buildings.length ≤ 5) :
  (spidey_swings buildings).getLast! < sum_widths buildings :=
sorry

/-
info: [76, 258, 457, 643, 748]
-/
-- #guard_msgs in
-- #eval spidey_swings [[162, 76], [205, 96], [244, 86], [212, 68], [174, 57], [180, 89], [208, 70], [214, 82], [181, 69], [203, 67]]

-- Apps difficulty: interview
-- Assurance level: unguarded