-- <vc-preamble>
def String.replicate (n : Nat) (s : String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spam (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spam_multiplication (n : Nat) : n ≤ 1000 → spam n = String.replicate n "hue" :=
  sorry

/-
info: 'hue'
-/
-- #guard_msgs in
-- #eval spam 1

/-
info: 'huehuehuehuehuehue'
-/
-- #guard_msgs in
-- #eval spam 6

/-
info: 'huehuehuehuehuehuehuehuehuehuehuehuehuehue'
-/
-- #guard_msgs in
-- #eval spam 14
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded