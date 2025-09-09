-- <vc-helpers>
-- </vc-helpers>

def solve_tshirts (n : Nat) (p : List Nat) (f : List Nat) (b : List Nat) (m : Nat) (bc : List Nat) : List Int :=
sorry

theorem no_matching_shirts_result
  (n : Nat)
  (p : List Nat)
  (f b : List Nat) 
  (m : Nat)
  (bc : List Nat)
  (h1 : n > 0)
  (h2 : n ≤ 5)
  (h3 : List.length p = n)
  (h4 : List.length f = n)
  (h5 : List.length b = n)
  (h6 : List.length bc > 0)
  (h7 : List.length bc ≤ 10)
  (h8 : ∀ x ∈ bc, x = 2 ∨ x = 3)
  (h9 : ∀ x ∈ f, x = 1)
  (h10 : ∀ x ∈ b, x = 1)
  (h11 : ∀ x ∈ p, x = 1) :
  let result := solve_tshirts n p f b m bc
  ∀ x ∈ result, x = -1 :=
sorry

/-
info: [200, 400, 300, 500, 911, -1]
-/
-- #guard_msgs in
-- #eval solve_tshirts 5 [300, 200, 400, 500, 911] [1, 2, 1, 2, 3] [2, 1, 3, 2, 1] 6 [2, 3, 1, 2, 1, 1]

/-
info: [1, 1000000000]
-/
-- #guard_msgs in
-- #eval solve_tshirts 2 [1000000000, 1] [1, 1] [1, 2] 2 [2, 1]

/-
info: [529469903]
-/
-- #guard_msgs in
-- #eval solve_tshirts 1 [529469903] [1] [3] 1 [3]

-- Apps difficulty: competition
-- Assurance level: unguarded