-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat := sorry

def combinations (xs : List α) (k : Nat) : List (List α) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit (n : Nat) (h : n ≤ 9) :
  digits n = [] := sorry

theorem two_digits (n : Nat) (h₁ : n ≥ 10) (h₂ : n ≤ 99) :
  let result := digits n
  result.length = 1 ∧ 
  result.head! = ((toString n).toList.map (fun c => c.toNat - '0'.toNat)).foldl (·+·) 0 := sorry

/-
info: [6, 7, 11]
-/
-- #guard_msgs in
-- #eval digits 156

/-
info: [9, 13, 17, 14, 6, 10, 7, 14, 11, 15]
-/
-- #guard_msgs in
-- #eval digits 81596

/-
info: [11, 8, 5, 13, 10, 7]
-/
-- #guard_msgs in
-- #eval digits 3852
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible