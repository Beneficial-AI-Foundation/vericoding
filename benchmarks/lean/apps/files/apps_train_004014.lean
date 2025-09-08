/-
Consider a pyramid made up of blocks. Each layer of the pyramid is a rectangle of blocks, and the dimensions of these rectangles increment as you descend the pyramid. So, if a layer is a `3x6` rectangle of blocks, then the next layer will be a `4x7` rectangle of blocks. A `1x10` layer will be on top of a `2x11` layer on top of a `3x12` layer, and so on.

## Task

Given the dimensions of a pyramid's topmost layer `w,l`, and its height `h` (aka the number of layers), return the total number of blocks in the pyramid.

## Examples

`num_blocks(1, 1, 2)` will return `5`. This pyramid starts with a `1x1` layer and has 2 layers total. So, there is 1 block in the first layer, and `2x2=4` blocks in the second. Thus, 5 is the total number of blocks.

`num_blocks(2, 4, 3)` will return `47`. This pyramid has 3 layers: `2x4`, `3x5`, and `4x6`. So, there are `47` blocks total.

## Notes

All parameters will always be postive nonzero integers.

Efficiency is important. There will be:

* 100 'small' cases with `w`, `l`, and `h` below `20`.
* 100 'big' cases with `w`, `l`, and `h` between `1e9` and `1e10`.
-/

-- <vc-helpers>
-- </vc-helpers>

def num_blocks (w l h : Nat) : Nat := sorry

theorem num_blocks_positive (w l h : Nat) (hw : w > 0) (hl : l > 0) (hh : h > 0) : 
  num_blocks w l h > 0 := sorry

theorem num_blocks_base_layer (w l h : Nat) (hw : w > 0) (hl : l > 0) (hh : h > 0) :
  num_blocks w l h ≥ w * l := sorry 

theorem num_blocks_all_layers (w l h : Nat) (hw : w > 0) (hl : l > 0) (hh : h > 0) :
  num_blocks w l h ≥ w * l * h := sorry

theorem num_blocks_symmetric (w l h : Nat) :
  num_blocks w l h = num_blocks l w h := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval num_blocks 1 1 2

/-
info: 47
-/
-- #guard_msgs in
-- #eval num_blocks 2 4 3

/-
info: 83540
-/
-- #guard_msgs in
-- #eval num_blocks 20 30 40

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible