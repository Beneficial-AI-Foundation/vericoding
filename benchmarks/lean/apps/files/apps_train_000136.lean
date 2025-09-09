-- <vc-helpers>
-- </vc-helpers>

def getMaxLen (nums : List Int) : Nat :=
  sorry

theorem getMaxLen_nonnegative (nums : List Int) : 
  getMaxLen nums ≥ 0 := sorry

theorem getMaxLen_upper_bound (nums : List Int) :
  getMaxLen nums ≤ nums.length := sorry

theorem getMaxLen_all_zeros {nums : List Int} (h : ∀ x ∈ nums, x = 0) : 
  getMaxLen nums = 0 := sorry

theorem getMaxLen_zeros_only (n : Nat) : 
  getMaxLen (List.replicate n 0) = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval getMaxLen [1, -2, -3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval getMaxLen [0, 1, -2, -3, -4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval getMaxLen [-1, -2, -3, 0, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded