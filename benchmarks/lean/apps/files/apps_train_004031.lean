-- <vc-preamble>
def solve (n k : Nat) : List Nat := sorry

def isStrictlyIncreasing (lst : List Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkSum (n : Nat) (lst : List Nat) : Bool := sorry

theorem solve_large_k (n k : Nat) (h1 : n > 0) (h2 : k > n) :
  (solve n k).length = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_k_equals_one (n : Nat) (h : n > 0) :
  let result := solve n 1
  result.length > 0 → result = [n] := sorry

/-
info: [2, 4, 6]
-/
-- #guard_msgs in
-- #eval solve 12 3

/-
info: [3, 6, 9]
-/
-- #guard_msgs in
-- #eval solve 18 3

/-
info: [2, 4, 6, 12]
-/
-- #guard_msgs in
-- #eval solve 24 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible