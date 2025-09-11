-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_number (divisors : List Nat) : Nat := sorry

def get_proper_divisors (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_number_preserves_input {divisors original : List Nat} 
  (h : original = divisors) :
  original = divisors := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_number [2, 3]

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_number [4, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_number [12, 3, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible