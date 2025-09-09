-- <vc-helpers>
-- </vc-helpers>

def split_carrots_min_time (n k : Nat) (nums : List Nat) : Nat :=
  sorry

theorem splits_res_nonneg 
  (n k : Nat) (nums : List Nat) 
  (h1 : ∀ x ∈ nums, x > 0) 
  (h2 : ∀ x ∈ nums, x ≤ 10^6)
  (h3 : nums.length > 0)  
  (h4 : nums.length ≤ 100)
  (h5 : k > 0)
  (h6 : k ≤ 10^3) :
  split_carrots_min_time n k nums ≥ 0 := sorry

theorem splits_res_nat
  (n k : Nat) (nums : List Nat)
  (h1 : ∀ x ∈ nums, x > 0) 
  (h2 : ∀ x ∈ nums, x ≤ 10^6)
  (h3 : nums.length > 0)
  (h4 : nums.length ≤ 100)
  (h5 : k > 0)
  (h6 : k ≤ 10^3) :
  split_carrots_min_time n k nums = split_carrots_min_time n k nums := sorry

theorem more_splits_less_time
  (n k : Nat) (nums : List Nat)
  (h1 : ∀ x ∈ nums, x > 0)
  (h2 : ∀ x ∈ nums, x ≤ 10^6)
  (h3 : nums.length > 0)
  (h4 : nums.length ≤ 100)
  (h5 : k > nums.length)
  (h6 : k ≤ 10^3) :
  split_carrots_min_time n k nums ≤ split_carrots_min_time n (k-1) nums := sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval split_carrots_min_time 3 6 [5, 3, 1]

/-
info: 91
-/
-- #guard_msgs in
-- #eval split_carrots_min_time 1 4 [19]

/-
info: 333333333334
-/
-- #guard_msgs in
-- #eval split_carrots_min_time 1 3 [1000000]

-- Apps difficulty: competition
-- Assurance level: guarded