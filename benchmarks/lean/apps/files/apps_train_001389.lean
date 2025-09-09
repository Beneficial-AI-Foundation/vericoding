-- <vc-helpers>
-- </vc-helpers>

def find_max_cost (n : Nat) (arr : List Int) : Int := sorry

theorem find_max_cost_is_min {n : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : n > 0)
  (h3 : ∀ x ∈ arr, x > 0)
  (h4 : ∀ x ∈ arr, x ≤ 1000) :
  ∀ y ∈ arr, find_max_cost n arr ≤ y := sorry

theorem find_max_cost_in_list {n : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : n > 0)
  (h3 : ∀ x ∈ arr, x > 0) :
  find_max_cost n arr ∈ arr := sorry

theorem find_max_cost_order_invariant {n : Nat} {arr₁ arr₂ arr₃ : List Int}
  (h1 : n = arr₁.length)
  (h2 : n = arr₂.length)
  (h3 : n = arr₃.length)
  (h4 : n > 1)
  (h5 : ∀ x ∈ arr₁, x > 0)
  (h6 : arr₂.toArray = arr₁.toArray)
  (h7 : arr₃.toArray = arr₁.toArray) :
  find_max_cost n arr₁ = find_max_cost n arr₂ ∧ 
  find_max_cost n arr₂ = find_max_cost n arr₃ := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_max_cost 2 #[7, 12]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_max_cost 3 #[5, 8, 10]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_cost 4 #[3, 7, 11, 15]

-- Apps difficulty: interview
-- Assurance level: guarded