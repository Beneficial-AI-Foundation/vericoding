/-
Given an array A of integers, a ramp is a tuple (i, j) for which i < j and A[i] <= A[j].  The width of such a ramp is j - i.
Find the maximum width of a ramp in A.  If one doesn't exist, return 0.

Example 1:
Input: [6,0,8,2,1,5]
Output: 4
Explanation: 
The maximum width ramp is achieved at (i, j) = (1, 5): A[1] = 0 and A[5] = 5.

Example 2:
Input: [9,8,1,0,1,9,4,0,4,1]
Output: 7
Explanation: 
The maximum width ramp is achieved at (i, j) = (2, 9): A[2] = 1 and A[9] = 1.

Note:

2 <= A.length <= 50000
0 <= A[i] <= 50000
-/

def max_width_ramp (nums : List Int) : Nat :=
  sorry

def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true 
  | [_] => true
  | x::y::rest => x ≤ y && isSorted (y::rest)

def isStrictlyDecreasing (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x::y::rest => x > y && isStrictlyDecreasing (y::rest)

-- <vc-helpers>
-- </vc-helpers>

def hasNoDups (l : List Int) : Bool :=
  match l with
  | [] => true
  | x::xs => !(xs.contains x) && hasNoDups xs

theorem max_width_ramp_non_negative (nums : List Int) :
  max_width_ramp nums ≥ 0 := 
  sorry

theorem max_width_ramp_upper_bound (nums : List Int) :
  max_width_ramp nums ≤ max 0 (nums.length - 1) :=
  sorry 

theorem max_width_ramp_small_lists (nums : List Int) :
  nums.length ≤ 1 → max_width_ramp nums = 0 :=
  sorry

theorem max_width_ramp_valid_ramp_exists (nums : List Int) (h : max_width_ramp nums > 0) :
  ∃ i j, ∃ (hi : i < nums.length) (hj : j < nums.length),
         i < j ∧ j - i ≥ max_width_ramp nums ∧ 
         (nums.get ⟨i, hi⟩) ≤ (nums.get ⟨j, hj⟩) :=
  sorry

theorem max_width_ramp_monotonic_increasing (nums : List Int) :
  nums.length > 1 →
  isSorted nums = true →
  max_width_ramp nums = nums.length - 1 :=
  sorry

theorem max_width_ramp_strictly_decreasing (nums : List Int) :
  nums.length > 0 →
  isStrictlyDecreasing nums = true →
  hasNoDups nums = true →
  max_width_ramp nums = 0 :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_width_ramp [6, 0, 8, 2, 1, 5]

/-
info: 7
-/
-- #guard_msgs in
-- #eval max_width_ramp [9, 8, 1, 0, 1, 9, 4, 0, 4, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_width_ramp [1, 0]

-- Apps difficulty: interview
-- Assurance level: unguarded