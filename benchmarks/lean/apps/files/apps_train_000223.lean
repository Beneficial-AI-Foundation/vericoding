def longestOnes (A : List Nat) (K : Nat) : Nat := sorry

def isConsecutiveOnes (A : List Nat) (n : Nat) : Prop := sorry

-- <vc-helpers>
-- </vc-helpers>

def maxConsecutiveOnes (A : List Nat) : Nat := sorry

theorem longestOnes_upper_bound (A : List Nat) (K : Nat) : 
  longestOnes A K ≤ A.length := sorry

theorem longestOnes_min_bound (A : List Nat) (K : Nat) (n : Nat) :
  isConsecutiveOnes A n → n ≤ longestOnes A K := sorry

theorem longestOnes_zero_k (A : List Nat) :
  longestOnes A 0 = maxConsecutiveOnes A := sorry

theorem longestOnes_large_k (A : List Nat) (K : Nat) :
  K ≥ A.length → longestOnes A K = A.length := sorry

theorem longestOnes_single_zero (K : Nat) :
  longestOnes [0] K = min 1 K := sorry

theorem longestOnes_single_one (K : Nat) :
  longestOnes [1] K = 1 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval longestOnes [1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0] 2

/-
info: 10
-/
-- #guard_msgs in
-- #eval longestOnes [0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1] 3

/-
info: 4
-/
-- #guard_msgs in
-- #eval longestOnes [1, 1, 1, 1] 2

-- Apps difficulty: interview
-- Assurance level: unguarded