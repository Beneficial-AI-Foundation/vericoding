-- <vc-helpers>
-- </vc-helpers>

def oddity (n : Nat) : String := sorry

theorem oddity_returns_valid_value (n : Nat) (h : n > 0) :
  oddity n = "odd" ∨ oddity n = "even" := sorry

theorem oddity_perfect_square_iff_odd (n : Nat) (h : n > 0) :
  (∃ k, n = k * k) ↔ oddity n = "odd" := sorry

theorem oddity_one :
  oddity 1 = "odd" := sorry

theorem oddity_two :
  oddity 2 = "even" := sorry

theorem oddity_four :
  oddity 4 = "odd" := sorry

/-
info: 'odd'
-/
-- #guard_msgs in
-- #eval oddity 1

/-
info: 'odd'
-/
-- #guard_msgs in
-- #eval oddity 16

/-
info: 'even'
-/
-- #guard_msgs in
-- #eval oddity 27

-- Apps difficulty: introductory
-- Assurance level: unguarded