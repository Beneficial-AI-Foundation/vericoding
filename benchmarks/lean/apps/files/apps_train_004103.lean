-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chameleon (chameleons : List Nat) (color : Nat) : Int := sorry

theorem chameleon_result_is_valid 
  (chameleons : List Nat) 
  (color : Nat)
  (h1 : chameleons.length = 3)
  (h2 : color ≤ 2) :
  let result := chameleon chameleons color
  (result = -1 ∨ result ≥ 0) ∧
  (result = -1 ∨ 
    ∃ a b c : Nat,
      (a > 0 ∨ c > 0) ∧ 
      (b - a) % 3 = 0 ∧ 
      result = b)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: -1
-/
-- #guard_msgs in
-- #eval chameleon [0, 0, 17] 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval chameleon [1, 1, 15] 2

/-
info: 35
-/
-- #guard_msgs in
-- #eval chameleon [34, 32, 35] 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded