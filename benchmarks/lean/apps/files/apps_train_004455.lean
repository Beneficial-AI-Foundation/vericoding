-- <vc-preamble>
def sequence (n : Nat) : Nat := sorry

theorem sequence_nonnegative (n : Nat) : 
  sequence n ≥ 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toBinaryString (n : Nat) : List Nat := sorry
def fromBase3 (digits : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_monotonic {n : Nat} (h : n > 0) : 
  sequence n > sequence (n - 1) := sorry

/- Helper functions for binary/base-3 conversion -/

/-
info: 0
-/
-- #guard_msgs in
-- #eval sequence 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval sequence 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval sequence 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval sequence 3

/-
info: 9
-/
-- #guard_msgs in
-- #eval sequence 4

/-
info: 7329
-/
-- #guard_msgs in
-- #eval sequence 334
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible