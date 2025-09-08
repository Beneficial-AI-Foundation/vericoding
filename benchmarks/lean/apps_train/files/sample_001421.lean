/-
Many things in this first paragraph are references to some pretty famous YouTube stars, so be careful about rephrasing. Thanks! 
Michael, Kevin and Jake are sharing a cake, in celebration of their Webby award. They named it VCake. Unlike other cakes they considered, this one has finite volume and surface area. It's shaped as a normal rectangular cake with dimensions R centimeters by C centimeters. For the purposes of this problem, we can forget about three dimensions and think of a cake as just a 2D rectangle.
Chef will now cut the cake into three pieces, one for each person. However, the cake's shape and Chef's really old tools pose a few restrictions:

- Chef can only cut the cake, or a cake piece, across a line parallel to one of its sides. 
- Chef can only cut the cake, or a cake piece, from end to end. That is, she cannot cut the cake partially. 
- Chef can only cut the cake, or a cake piece, such that the sides of the resulting pieces (which will be rectangular in shape) are integers. 

In addition, Michael, Kevin and Jake also have a few preferences of their own:

- They want their pieces to be connected (in one piece), and rectangular in shape.
- Michael wants his piece to have an area exactly M square centimeters. (Again, forget about a third dimension.)
- Kevin wants his piece to have an area exactly K square centimeters.
- Jake wants his piece to have an area exactly J square centimeters.

With these restrictions, Chef is at a loss. Is it possible for Chef to accomplish this task? Please note that the entire cake should be used. There should be no leftover cake.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
Each test case consists of a single line containing five space separated integers R, C M, K and J.

-----Output-----
For each test case, output a single line containing either “Yes” or “No” (without quotes), denoting whether Chef can accomplish the task or not.

-----Constraints-----
- 1 ≤ T ≤ 105
- 1 ≤ R, C ≤ 109
- 1 ≤ M, K, J ≤ 1018

-----Example-----
Input:4
4 5 10 4 6
4 5 6 10 4
4 5 4 6 10
2 2 2 2 2

Output:Yes
Yes
Yes
No

-----Explanation-----
Example case 1. In this case, Chef can accomplish the task by doing the following slicing.  
pre tt
_ _ _ _ _       _ _ _ _ _       _ _ _ _ _       _________ 
|         |     |         |     |         |     |M M M M M|
|         | -- |_ _ _ _ _| -- |_ _ _ _ _| -- |M_M_M_M_M|
|         |     |         |     |     |   |     |J J J|K K|
|_ _ _ _ _|     |_ _ _ _ _|     |_ _ _|_ _|     |J_J_J|K_K|
/tt /pre
I'll make an image if I have time 
Example case 4. Here, Michael, Kevin and Jake each wants a piece with area 2, but the total area of the cake is only 2×2 = 4. This means the task is impossible.
-/

-- <vc-helpers>
-- </vc-helpers>

def can_slice_cake (r c m k j : Nat) : String := sorry

theorem can_slice_cake_valid_output (r c m k j : Nat) (h1 : r > 0) (h2 : c > 0) 
    (h3 : m > 0) (h4 : k > 0) (h5 : j > 0) :
  can_slice_cake r c m k j = "Yes" ∨ can_slice_cake r c m k j = "No" := sorry

theorem can_slice_cake_area_mismatch (r c m k j : Nat) (h1 : r > 0) (h2 : c > 0)
    (h3 : m > 0) (h4 : k > 0) (h5 : j > 0) (h6 : r * c ≠ m + k + j) :
  can_slice_cake r c m k j = "No" := sorry

theorem can_slice_cake_equal_pieces (r c : Nat) (h1 : r > 0) (h2 : c > 0)
    (h3 : r * c % 3 = 0) (h4 : (r * c) / 3 ≤ max r c) :
  can_slice_cake r c ((r * c) / 3) ((r * c) / 3) ((r * c) / 3) = "Yes" := sorry

theorem can_slice_cake_piece_exceeds_area (r c m k j : Nat) (h1 : r > 0) (h2 : c > 0)
    (h3 : m > r * c ∨ k > r * c ∨ j > r * c) :
  can_slice_cake r c m k j = "No" := sorry

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_slice_cake 4 5 10 4 6

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval can_slice_cake 4 5 6 10 4

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval can_slice_cake 2 2 2 2 2

-- Apps difficulty: interview
-- Assurance level: unguarded