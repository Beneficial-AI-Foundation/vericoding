/-
In this Kata, you will be given an array of integers and your task is to return the number of arithmetic progressions of size `3` that are possible from that list. In each progression, the differences between the elements must be the same.

```
[1, 2, 3, 5, 7, 9] ==> 5
// [1, 2, 3], [1, 3, 5], [1, 5, 9], [3, 5, 7], and [5, 7, 9]
```

All inputs will be sorted. More examples in test cases. 

Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def solve (arr : List Int) : Int := sorry

theorem solve_type (arr : List Int) (h: arr.length ≥ 3 ∧ arr.length ≤ 20) : 
  solve arr ≥ 0 := sorry

theorem solve_shift_invariant (arr : List Int) (shift : Int)
    (h: arr.length ≥ 3 ∧ arr.length ≤ 20) :
  solve arr = solve (arr.map (· + shift)) := sorry

theorem solve_scale_invariant (arr : List Int) (scale : Int)
    (h: arr.length ≥ 3 ∧ arr.length ≤ 20) (h2: scale ≠ 0) :
  solve arr = solve (arr.map (· * scale)) := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve [1, 2, 3, 4, 5]

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve [1, 2, 3, 5, 7, 9]

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve [0, 5, 8, 9, 11, 13, 14, 16, 17, 19]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible