-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeat_sequence_len (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeat_sequence_len_positive (n : Nat) 
  (h : n > 0) :
  repeat_sequence_len n > 0 := by sorry 

theorem repeat_sequence_len_idempotent (n : Nat)
  (h : n > 0) :
  repeat_sequence_len (repeat_sequence_len n) = repeat_sequence_len n := by sorry

theorem sequence_convergence (n : Nat)
  (h : n > 0) :
  let final := repeat_sequence_len n
  final = 1 ∨ final = 89 := by sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval repeat_sequence_len 1

/-
info: 8
-/
-- #guard_msgs in
-- #eval repeat_sequence_len 85

/-
info: 8
-/
-- #guard_msgs in
-- #eval repeat_sequence_len 810
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded