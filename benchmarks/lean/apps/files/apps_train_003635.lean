/-
# The Invitation

Most of us played with toy blocks growing up. It was fun and you learned stuff. So what else can you do but rise to the challenge when a 3-year old exclaims, "Look, I made a square!", then pointing to a pile of blocks, "Can _you_ do it?"

# These Blocks

Just to play along, of course we'll be viewing these blocks in two dimensions. Depth now being disregarded, it turns out the pile has four different sizes of block: `1x1`, `1x2`, `1x3`, and `1x4`. The smallest one represents the area of a square, the other three are rectangular, and all differ by their width. Integers matching these four widths are used to represent the blocks in the input.

# This Square

Well, the kid made a `4x4` square from this pile, so you'll have to match that. Noticing the way they fit together, you realize the structure must be built in fours rows, one row at a time, where the blocks must be placed horizontally. With the known types of block, there are five types of row you could build:

* 1 four-unit block
* 1 three-unit block plus 1 one-unit bock (in either order)
* 2 two-unit blocks
* 1 two-unit block plus 2 one-unit blocks (in any order)
* 4 one-unit blocks

Amounts for all four of the block sizes in the pile will each vary from `0` to `16`. The total size of the pile will also vary from `0` to `16`. The order of rows is irrelevant. A valid square doesn't have to use up all the given blocks.

# Some Examples

Given `1, 3, 2, 2, 4, 1, 1, 3, 1, 4, 2` there are many ways you could construct a square. Here are three possibilities, as described by their four rows:

* 1 four-unit block
* 2 two-unit blocks
* 1 four-unit block
* 4 one-unit blocks
>
* 1 three-unit block plus 1 one-unit block
* 2 two-unit blocks
* 1 four-unit block
* 1 one-unit block plus 1 three-unit block
>
* 2 two-unit blocks
* 1 three-unit block plus 1 one-unit block
* 1 four-unit block
* 2 one-unit blocks plus 1 two-unit block
>

Given `1, 3, 2, 4, 3, 3, 2` there is no way to complete the task, as you could only build three rows of the correct length. The kid will not be impressed.

* 2 two-unit blocks
* 1 three-unit block plus 1 one-unit block
* 1 four-unit block
* (here only sadness)
>

# Input
```python
blocks ~ a random list of integers (1 <= x <= 4)
```
# Output
```python
True or False ~ whether you can build a square
```
# Enjoy!

If interested, I also have [this kata](https://www.codewars.com/kata/5cb7baa989b1c50014a53333) as well as [this other kata](https://www.codewars.com/kata/5cb5eb1f03c3ff4778402099) to consider solving.
-/

def build_square (blocks: List Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + list_sum xs

theorem sum_16_if_buildable {blocks : List Nat} :
  build_square blocks = true → 
  list_sum blocks ≥ 16 :=
sorry

theorem input_unchanged {blocks : List Nat} :
  build_square blocks = b →
  blocks = blocks :=
sorry

theorem invalid_pieces {blocks : List Nat} : 
  (∀ x ∈ blocks, x < 1 ∨ x > 4) →
  build_square blocks = false :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval build_square [1, 1, 1, 1, 1, 1, 1, 2, 3, 4]

/-
info: False
-/
-- #guard_msgs in
-- #eval build_square [1, 3, 2, 4, 3, 3, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval build_square [4, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded