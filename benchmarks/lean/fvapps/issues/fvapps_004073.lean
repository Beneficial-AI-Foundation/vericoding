-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest (n : Nat) (xs : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_size {n : Nat} {xs : List Int} 
  (h_nonempty : xs ≠ []) 
  (h_n_valid : n ≤ xs.length) :
  (largest n xs).length = n :=
  sorry

theorem largest_elements {n : Nat} {xs : List Int}
  (h_nonempty : xs ≠ [])
  (h_n_valid : n ≤ xs.length) :
  ∀ x ∈ largest n xs, x ∈ xs :=
  sorry

theorem largest_order {n : Nat} {xs : List Int}
  (h_nonempty : xs ≠ [])
  (h_n_valid : n ≤ xs.length)
  (i j : Nat) (h_i : i < n) (h_j : j < n) (h : i < j) :
  let result := largest n xs
  let i' : Fin result.length := ⟨i, by simp [largest_size h_nonempty h_n_valid, h_i]⟩
  let j' : Fin result.length := ⟨j, by simp [largest_size h_nonempty h_n_valid, h_j]⟩
  result.get i' ≥ result.get j' :=
  sorry

theorem largest_max_property {n : Nat} {xs : List Int}
  (h_nonempty : xs ≠ [])
  (h_n_valid : n ≤ xs.length) :
  ∀ x ∈ xs, x ∉ largest n xs → x ≤ (largest n xs).head! :=
  sorry

theorem largest_full_list {xs : List Int}
  (h_nonempty : xs ≠ []) :
  largest xs.length xs = xs :=
  sorry

/-
info: [6, 7]
-/
-- #guard_msgs in
-- #eval largest 2 [7, 6, 5, 4, 3, 2, 1]

/-
info: [9, 10]
-/
-- #guard_msgs in
-- #eval largest 2 [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]

/-
info: [3, 4, 5]
-/
-- #guard_msgs in
-- #eval largest 3 [1, 2, 3, 4, 5]
-- </vc-theorems>