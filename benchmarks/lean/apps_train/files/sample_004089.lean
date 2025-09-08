/-
Your company, [Congo Pizza](http://interesting-africa-facts.com/Africa-Landforms/Congo-Rainforest-Facts.html), is the second-largest online frozen pizza retailer. You own a number of international warehouses that you use to store your frozen pizzas, and you need to figure out how many crates of pizzas you can store at each location.

Congo recently standardized its storage containers: all pizzas fit inside a *cubic crate, 16-inchs on a side*. The crates are super tough so you can stack them as high as you want.

Write a function `box_capacity()` that figures out how many crates you can store in a given warehouse. The function should take three arguments: the length, width, and height of your warehouse (in feet) and should return an integer representing the number of boxes you can store in that space.

For example: a warehouse 32 feet long, 64 feet wide, and 16 feet high can hold 13,824 boxes because you can fit 24 boxes across, 48 boxes deep, and 12 boxes high, so `box_capacity(32, 64, 16)` should return `13824`.
-/

-- <vc-helpers>
-- </vc-helpers>

def box_capacity (length width height : Nat) : Nat := sorry

theorem box_capacity_nonneg (l w h : Nat) :
  box_capacity l w h ≥ 0 := sorry

theorem box_capacity_monotonic_length (l w h : Nat) :
  box_capacity (l + 1) w h ≥ box_capacity l w h := sorry

theorem box_capacity_monotonic_width (l w h : Nat) :
  box_capacity l (w + 1) h ≥ box_capacity l w h := sorry

theorem box_capacity_monotonic_height (l w h : Nat) :
  box_capacity l w (h + 1) ≥ box_capacity l w h := sorry

theorem box_capacity_small_dim (w h : Nat) :
  box_capacity 1 w h = 0 := sorry

/-
info: 13824
-/
-- #guard_msgs in
-- #eval box_capacity 32 64 16

/-
info: 3375
-/
-- #guard_msgs in
-- #eval box_capacity 20 20 20

/-
info: 27000
-/
-- #guard_msgs in
-- #eval box_capacity 80 40 20

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible