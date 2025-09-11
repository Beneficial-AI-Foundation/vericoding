-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f (n : Nat) : Nat := sorry

def isPrime (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem f_always_positive (n : Nat) (h : n > 0) : 
  f n > 0 := sorry

/-
info: 4200
-/
-- #guard_msgs in
-- #eval f 24500

/-
info: 1
-/
-- #guard_msgs in
-- #eval f 997

/-
info: 10
-/
-- #guard_msgs in
-- #eval f 25
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible