/-
The Spelling Bee bees are back...

# How many bees are in the beehive?

* bees can be facing UP, DOWN, LEFT, RIGHT, and now also _diagonally_ up/down/left/right
* bees can share parts of other bees

## Examples

Ex1
```
bee.bee     
.e..e..
.b..eeb
```
_Answer: 5_

Ex2
```
beee..     
eeb.e.
ebee.b
```
_Answer: 7_
-/

def Grid := List String

def GridList := List (List Char)

-- <vc-helpers>
-- </vc-helpers>

def how_many_bees (grid : Grid) : Nat := sorry
def how_many_bees_list (grid : GridList) : Nat := sorry

theorem how_many_bees_nonnegative (grid : Grid) :
  how_many_bees grid ≥ 0 := sorry

theorem grid_list_equiv (grid : Grid) :
  how_many_bees grid = how_many_bees_list (grid.map (·.data)) := sorry

theorem empty_grid :
  how_many_bees [] = 0 := sorry

theorem bees_upper_bound {grid : Grid} (h : grid ≠ []) :
  how_many_bees grid ≤ grid.length * grid.head!.length * 2 := sorry

theorem reverse_grid_equiv (grid : Grid) :
  let reversed := grid.map (fun s => ⟨s.data.reverse⟩)
  how_many_bees grid = how_many_bees reversed := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval how_many_bees ["bee.bee", ".e..e..", ".b..eeb"]

/-
info: 7
-/
-- #guard_msgs in
-- #eval how_many_bees ["beee..", "eeb.e.", "ebee.b"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval how_many_bees []

-- Apps difficulty: introductory
-- Assurance level: unguarded