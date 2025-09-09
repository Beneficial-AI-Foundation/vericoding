-- <vc-helpers>
-- </vc-helpers>

def sc_perm_comb (n : Nat) : Nat := sorry

theorem sc_perm_comb_non_negative (n : Nat) :
  sc_perm_comb n ≥ 0 := sorry

theorem sc_perm_comb_geq_input (n : Nat) :
  sc_perm_comb n ≥ n := sorry 

theorem sc_perm_comb_single_digit (n : Nat) (h : n ≤ 9) :
  sc_perm_comb n = n := sorry

theorem sc_perm_comb_zero :
  sc_perm_comb 0 = 0 := sorry

theorem sc_perm_comb_two_digits (n : Nat) (h1 : n ≥ 10) (h2 : n ≤ 99) 
    (h3 : n % 10 ≠ n / 10) :
  sc_perm_comb n ≥ n + (n % 10 * 10 + n / 10) := sorry

/-
info: 3675
-/
-- #guard_msgs in
-- #eval sc_perm_comb 348

/-
info: 1631
-/
-- #guard_msgs in
-- #eval sc_perm_comb 340

/-
info: 369
-/
-- #guard_msgs in
-- #eval sc_perm_comb 333

-- Apps difficulty: introductory
-- Assurance level: unguarded