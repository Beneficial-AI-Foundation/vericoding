-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_overlap (img1 img2 : Matrix) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_matrix_property 
  (n : Nat) (img1 img2 : Matrix)
  (h1 : img1.length = n)
  (h2 : img2.length = n) 
  (h3 : ∀ row, row ∈ img1 → row.length = n)
  (h4 : ∀ row, row ∈ img2 → row.length = n)
  (h5 : ∀ row ∈ img1, ∀ x ∈ row, x ≤ 1)
  (h6 : ∀ row ∈ img2, ∀ x ∈ row, x ≤ 1) :
  let result := largest_overlap img1 img2
  result ≥ 0 ∧ result ≤ n * n :=
sorry

theorem zero_overlap_property (n : Nat) (h : n > 0) :
  let ones_matrix := List.replicate n (List.replicate n 1)
  let zeros_matrix := List.replicate n (List.replicate n 0)
  largest_overlap ones_matrix zeros_matrix = 0 :=
sorry

theorem symmetry_property
  (n : Nat) (img1 img2 : Matrix)
  (h1 : img1.length = n)
  (h2 : img2.length = n)
  (h3 : ∀ row, row ∈ img1 → row.length = n)
  (h4 : ∀ row, row ∈ img2 → row.length = n)
  (h5 : ∀ row ∈ img1, ∀ x ∈ row, x ≤ 1)
  (h6 : ∀ row ∈ img2, ∀ x ∈ row, x ≤ 1) :
  largest_overlap img1 img2 = largest_overlap img2 img1 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval largest_overlap [[1, 1, 0], [0, 1, 0], [0, 1, 0]] [[0, 0, 0], [0, 1, 1], [0, 0, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval largest_overlap [[1]] [[1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval largest_overlap [[0]] [[0]]
-- </vc-theorems>