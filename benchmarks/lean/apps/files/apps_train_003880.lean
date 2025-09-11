-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def VALID_NOTES := ["A", "A#", "B", "C", "C#", "D", "D#", "E", "F", "F#", "G", "G#"]

def which_note (n : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem note_is_valid (n : Nat) (h : n > 0) : 
  which_note n ∈ VALID_NOTES := sorry 

theorem note_wraps_after_88 (n : Nat) (h : n > 0) :
  which_note n = which_note (n + 88) := sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval which_note 1

/-
info: 'D'
-/
-- #guard_msgs in
-- #eval which_note 42

/-
info: 'C'
-/
-- #guard_msgs in
-- #eval which_note 92
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded