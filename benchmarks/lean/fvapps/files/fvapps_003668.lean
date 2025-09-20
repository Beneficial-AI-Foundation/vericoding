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
-- </vc-theorems>