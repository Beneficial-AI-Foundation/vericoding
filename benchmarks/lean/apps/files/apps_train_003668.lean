-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat := sorry

def final_attack_value (x : Nat) (monster_list : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem final_attack_value_empty {x : Nat} (hx : x > 0) :
    final_attack_value x [] = x := sorry

/-
info: 110
-/
-- #guard_msgs in
-- #eval final_attack_value 50 [50, 105, 200]

/-
info: 205
-/
-- #guard_msgs in
-- #eval final_attack_value 20 [30, 20, 15, 40, 100]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible