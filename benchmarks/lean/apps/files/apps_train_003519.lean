-- <vc-helpers>
-- </vc-helpers>

def layers (n : Nat) : Nat := sorry

theorem layers_positive (n : Nat) (h : n > 0) : 
  layers n > 0 := sorry

theorem layer_fits_n (n : Nat) (h : n > 0) :
  let k := layers n
  (2*k - 1)^2 ≥ n := sorry

theorem prev_layer_too_small (n : Nat) (h : n > 0) (h2 : layers n > 1) :
  let k := layers n
  (2*(k-1) - 1)^2 < n := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval layers 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval layers 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval layers 25

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible