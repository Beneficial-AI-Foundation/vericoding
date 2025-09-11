-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arr : Nat → List Nat
| n => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arr_length (n : Nat) : (arr n).length = n := sorry

theorem arr_sequence (n : Nat) (i : Nat) (h : i < n) : 
  (arr n).get ⟨i, by rw [arr_length n]; exact h⟩ = i := sorry 

theorem arr_empty : arr 0 = [] := sorry

/-
info: [0, 1, 2, 3]
-/
-- #guard_msgs in
-- #eval arr 4

/-
info: []
-/
-- #guard_msgs in
-- #eval arr 0

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval arr 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible