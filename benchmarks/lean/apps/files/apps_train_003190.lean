-- <vc-helpers>
-- </vc-helpers>

def find_dup (arr : List Nat) : Nat := sorry

theorem find_dup_correct (n : Nat) (duplicate : Nat) 
  (h1 : n ≥ 2)
  (h2 : duplicate < n)
  (h3 : duplicate > 0)
  (arr : List Nat)
  (h4 : arr = (List.range (n-1)).append [duplicate]) :
  find_dup arr = duplicate ∧ 
  (arr.filter (λ x => x = duplicate)).length = 2 ∧
  ∀ x ∈ arr, x ≤ n-1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_dup [1, 1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_dup [1, 2, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_dup [5, 4, 3, 2, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded