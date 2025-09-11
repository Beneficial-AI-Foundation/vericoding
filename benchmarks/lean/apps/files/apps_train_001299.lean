-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 1000000007

def count_weighted_integers (n: Nat) (w: Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_weighted_integers_non_negative 
  (n: Nat) (w: Int)
  (h1: n ≥ 2) (h2: n ≤ 1000) 
  (h3: w ≥ -20) (h4: w ≤ 20) :
  count_weighted_integers n w ≥ 0 := sorry

theorem count_weighted_integers_impossible_weight
  (n: Nat) (w: Int)
  (h1: n ≥ 2) (h2: n ≤ 1000)
  (h3: w > 9 ∨ w < -9) :
  count_weighted_integers n w = 0 := sorry

theorem count_weighted_integers_mod_bounds
  (n: Nat) (w: Int)
  (h1: n ≥ 2) (h2: n ≤ 1000)
  (h3: w ≥ -20) (h4: w ≤ 20) :
  0 ≤ count_weighted_integers n w ∧ count_weighted_integers n w < MOD := sorry

theorem count_weighted_integers_zero_weight
  (n: Nat)
  (h1: n ≥ 2) (h2: n ≤ 100) :
  count_weighted_integers n 0 = (((10 ^ (n-2)) % MOD) * 9) % MOD := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_weighted_integers 2 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_weighted_integers 2 10

/-
info: 80
-/
-- #guard_msgs in
-- #eval count_weighted_integers 3 -2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded