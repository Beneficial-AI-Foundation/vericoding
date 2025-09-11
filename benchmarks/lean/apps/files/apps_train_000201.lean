-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMaxForm (strs : List String) (m n : Nat) : Nat := sorry

theorem findMaxForm_bounds {strs : List String} {m n : Nat} (h : strs.length > 0) :
  findMaxForm strs m n ≤ strs.length ∧ findMaxForm strs m n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findMaxForm_empty_string {strs : List String} (h : strs.length > 0) :
  findMaxForm (strs ++ [""] ) 1 1 ≤ findMaxForm strs 1 1 + 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval findMaxForm ["10", "0001", "111001", "1", "0"] 5 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval findMaxForm ["10", "0", "1"] 1 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval findMaxForm ["10", "0"] 1 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible