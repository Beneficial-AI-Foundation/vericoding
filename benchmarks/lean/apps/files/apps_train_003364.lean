-- <vc-helpers>
-- </vc-helpers>

def odd_ones_out (xs : List Int) : List Int := sorry

theorem odd_ones_out_preserves_pairs {xs : List Int} (h : xs ≠ []) :
  odd_ones_out xs = xs.filter (fun x => (xs.count x) % 2 = 0) := sorry

theorem odd_ones_out_elements_from_input {xs : List Int} (h : xs ≠ []) :
  ∀ x ∈ odd_ones_out xs, x ∈ xs := sorry 

theorem odd_ones_out_even_counts {xs : List Int} (h : xs ≠ []) :
  ∀ x ∈ odd_ones_out xs, (odd_ones_out xs).count x % 2 = 0 := sorry

theorem odd_ones_out_maintains_order {xs : List Int} (h : xs ≠ []) : 
  odd_ones_out xs = xs.filter (fun x => xs.count x % 2 = 0) := sorry

/-
info: [1, 1]
-/
-- #guard_msgs in
-- #eval odd_ones_out [1, 2, 3, 1, 3, 3]

/-
info: [75, 68, 75, 68]
-/
-- #guard_msgs in
-- #eval odd_ones_out [75, 68, 75, 47, 68]

/-
info: [100, 100, 100, 100]
-/
-- #guard_msgs in
-- #eval odd_ones_out [100, 100, 5, 5, 100, 50, 68, 50, 68, 50, 68, 5, 100]

-- Apps difficulty: introductory
-- Assurance level: guarded