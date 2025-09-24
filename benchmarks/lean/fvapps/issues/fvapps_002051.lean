-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_fountain_beauty (n : Nat) (coins : Nat) (diamonds : Nat) (fountains : List Fountain) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_fountain_beauty_non_negative (n : Nat) (coins : Nat) (diamonds : Nat) 
    (fountains : List Fountain) :
  max_fountain_beauty n coins diamonds fountains ≥ 0 := sorry

theorem max_fountain_beauty_zero_when_insufficient_fountains (n : Nat) (coins : Nat) 
    (diamonds : Nat) (fountains : List Fountain) :
  let coin_fountains := fountains.filter (fun f => f.type = 'C' ∧ f.price ≤ coins)
  let diamond_fountains := fountains.filter (fun f => f.type = 'D' ∧ f.price ≤ diamonds)
  ¬(coin_fountains.length ≥ 2 ∨ diamond_fountains.length ≥ 2) ∧ 
  ¬(coin_fountains.length ≥ 1 ∧ diamond_fountains.length ≥ 1) →
  max_fountain_beauty n coins diamonds fountains = 0 := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval max_fountain_beauty 3 7 6 [(10, 8, "C"), (4, 3, "C"), (5, 6, "D")]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_fountain_beauty 2 4 5 [(2, 5, "C"), (2, 1, "D")]

/-
info: 10
-/
-- #guard_msgs in
-- #eval max_fountain_beauty 3 10 10 [(5, 5, "C"), (5, 5, "C"), (10, 11, "D")]
-- </vc-theorems>