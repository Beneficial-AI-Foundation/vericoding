-- <vc-preamble>
def maxEqualSeq : List Int → Nat 
  | [] => 1
  | [x] => 1 
  | x::y::xs => if x = y 
                then 1 + maxEqualSeq (y::xs)
                else max 1 (maxEqualSeq (y::xs))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestSubarray (nums : List Int) (limit : Nat) : Nat := sorry

theorem longestSubarray_result_bounds 
  {nums : List Int} {limit : Nat} (h : nums ≠ []) : 
  1 ≤ (longestSubarray nums limit) ∧ (longestSubarray nums limit) ≤ nums.length := sorry

/- There exists a valid subarray of length equal to the result -/
-- </vc-definitions>

-- <vc-theorems>
theorem longestSubarray_exists_valid_window
  {nums : List Int} {limit : Nat} (h : nums ≠ []) :
  ∃ i, i + (longestSubarray nums limit) ≤ nums.length ∧ 
    let window := nums.take (i + (longestSubarray nums limit)) |>.drop i
    (window.maximum? |>.getD 0) - (window.minimum? |>.getD 0) ≤ limit := sorry

/- No larger valid window exists -/

theorem longestSubarray_optimal
  {nums : List Int} {limit : Nat} (h : nums ≠ []) :
  ∀ i len, i + len ≤ nums.length → len > (longestSubarray nums limit) →
    let window := nums.take (i + len) |>.drop i
    (window.maximum? |>.getD 0) - (window.minimum? |>.getD 0) > limit := sorry

/- For zero limit, result equals longest sequence of equal numbers -/

theorem longestSubarray_zero_limit
  {nums : List Int} (h : nums ≠ []) :
  longestSubarray nums 0 = maxEqualSeq nums := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval longestSubarray [8, 2, 4, 7] 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval longestSubarray [10, 1, 2, 4, 7, 2] 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval longestSubarray [4, 2, 2, 2, 4, 4, 2, 2] 0
-- </vc-theorems>