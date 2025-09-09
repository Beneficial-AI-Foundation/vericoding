def maximum (xs : List Int) : Int := xs.foldl max 0

def sum (xs : List Int) : Int := xs.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

def max_sum (arr : List Int) : Int := sorry

def solve (arr : List Int) (k : Nat) : Int := sorry

theorem solve_vs_max_sum (arr : List Int) (k : Nat) (h : arr ≠ []) (hk : k > 0) :
  solve arr k ≥ max_sum arr := sorry

theorem solve_monotonic_k (arr : List Int) (k : Nat) (h : arr ≠ []) (hk : k > 1) :
  solve arr k ≥ solve arr 1 := sorry

theorem solve_k1_equals_maxsum (arr : List Int) (h : arr ≠ []) :
  solve arr 1 = max_sum arr := sorry

theorem solve_concatenation (arr : List Int) (h : arr ≠ []) :
  solve arr 2 ≥ max_sum (arr ++ arr) := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve [1, 2] 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve [1, -2, 1] 2

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve [-1, -2, -3] 4

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible