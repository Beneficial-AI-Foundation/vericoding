-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000000007

def nthMagicalNumber (n a b : Nat) : Nat :=
  sorry

theorem same_number_property {n : Nat} (h : n > 0) (h2 : n ≤ 10000) :
  nthMagicalNumber n 2 2 = (2 * n) % MOD := by
  sorry

theorem monotonic_increasing {a b : Nat} 
  (ha : a > 0) (hb : b > 0) (ha2 : a ≤ 100) (hb2 : b ≤ 100) :
  nthMagicalNumber 1 a b < nthMagicalNumber 2 a b := by
  sorry

theorem result_bounds {n a b : Nat}
  (hn : n > 0) (ha : a > 0) (hb : b > 0)
  (hn2 : n ≤ 100) (ha2 : a ≤ 100) (hb2 : b ≤ 100) :
  0 ≤ nthMagicalNumber n a b ∧ nthMagicalNumber n a b < MOD := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_magical_number 1 2 3

/-
info: 6
-/
-- #guard_msgs in
-- #eval nth_magical_number 4 2 3

/-
info: 10
-/
-- #guard_msgs in
-- #eval nth_magical_number 5 2 4

-- Apps difficulty: interview
-- Assurance level: guarded