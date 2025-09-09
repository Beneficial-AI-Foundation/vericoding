def sumOfDigits (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def rthn_between (a b : Int) : List Int :=
  sorry

theorem rthn_between_ordered_bounds {a b : Int} (h : a ≤ b) (h₁ : 0 ≤ a) (h₂ : b ≤ 10000) :
  let result := rthn_between a b
  -- Result is sorted
  (∀ i j, i < j → i < List.length result → j < List.length result → 
    result[i]! ≤ result[j]!) ∧
  -- All numbers within bounds
  (∀ x ∈ result, a ≤ x ∧ x ≤ b) ∧
  -- Each number divisible by sum of its digits
  (∀ x ∈ result, x % sumOfDigits (Int.toNat x) = 0) :=
  sorry

theorem rthn_between_same_bounds {n : Int} (h : 0 ≤ n) (h₁ : n ≤ 10000) :
  let result := rthn_between n n
  (result ≠ [] → 
    List.length result = 1 ∧
    result[0]! = n ∧ 
    n % sumOfDigits (Int.toNat n) = 0) :=
  sorry

theorem rthn_between_inverted_bounds {n : Int} (h : 0 ≤ n) (h₁ : n ≤ 10000) :
  rthn_between n (n-1) = [] :=
  sorry

theorem rthn_between_edge_cases :
  (rthn_between 0 0 = []) ∧
  (rthn_between (-1) 10 = [10]) :=
  sorry

/-
info: [10, 12, 18, 20]
-/
-- #guard_msgs in
-- #eval rthn_between 0 20

/-
info: [200, 201, 204, 207, 209, 210]
-/
-- #guard_msgs in
-- #eval rthn_between 200 210

/-
info: []
-/
-- #guard_msgs in
-- #eval rthn_between 2200 2300

-- Apps difficulty: introductory
-- Assurance level: guarded