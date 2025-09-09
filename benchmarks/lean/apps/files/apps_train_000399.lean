-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000000007

def kConcatenationMaxSum (arr : List Int) (k : Nat) : Int :=
  sorry

theorem kconcat_nonnegative (arr : List Int) (k : Nat) :
  k > 0 → kConcatenationMaxSum arr k ≥ 0 := sorry

theorem kconcat_mod_bound (arr : List Int) (k : Nat) :
  k > 0 → kConcatenationMaxSum arr k < MOD := sorry

theorem kconcat_k1_maxsubarray (arr : List Int) :
  kConcatenationMaxSum arr 1 = kConcatenationMaxSum arr 1 := sorry

theorem kconcat_empty (k : Nat) :
  k > 0 → kConcatenationMaxSum [] k = 0 := sorry

theorem kconcat_monotone_positive (arr : List Int) (k : Nat) :
  k > 1 →
  (arr.foldl (· + ·) 0 > 0) →
  kConcatenationMaxSum arr k ≥ kConcatenationMaxSum arr (k-1) := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval kConcatenationMaxSum [1, 2] 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval kConcatenationMaxSum [1, -2, 1] 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval kConcatenationMaxSum [-1, -2] 7

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible