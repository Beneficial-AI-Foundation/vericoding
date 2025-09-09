-- <vc-helpers>
-- </vc-helpers>

def sharkovsky (a b : Nat) : Bool := 
  sorry

theorem sharkovsky_reflexive {a : Nat} :
  ¬ sharkovsky a a := 
  sorry

theorem sharkovsky_antisymmetric {a b : Nat} :
  a ≠ b → ¬(sharkovsky a b ∧ sharkovsky b a) :=
  sorry

theorem sharkovsky_transitive {a b c : Nat} :
  sharkovsky a b → sharkovsky b c → sharkovsky a c :=
  sorry

theorem odd_precedes_power_of_two {a : Nat} (h : a ≥ 3) (h2 : a % 2 = 1) :
  sharkovsky a (2^4) :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval sharkovsky 18 12

/-
info: True
-/
-- #guard_msgs in
-- #eval sharkovsky 3 9

/-
info: True
-/
-- #guard_msgs in
-- #eval sharkovsky 10 16

/-
info: False
-/
-- #guard_msgs in
-- #eval sharkovsky 1 22

/-
info: False
-/
-- #guard_msgs in
-- #eval sharkovsky 32 1024

/-
info: False
-/
-- #guard_msgs in
-- #eval sharkovsky 17 17

-- Apps difficulty: introductory
-- Assurance level: unguarded