-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_chance (n : Nat) (x : Nat) (a : Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem probability_bounds (n : Nat) (x : Nat) (a : Nat) 
  (h1 : n > 0) (h2 : x ≤ n) (h3 : a ≤ n) :
  0 ≤ get_chance n x a ∧ get_chance n x a ≤ 1 :=
  sorry

theorem zero_laxatives (n : Nat) (a : Nat)
  (h1 : n > 0) (h2 : a ≤ n) :
  get_chance n 0 a = 1 :=
  sorry

theorem all_laxatives (n : Nat) (a : Nat) 
  (h1 : n > 0) (h2 : a ≤ n) :
  get_chance n n a = 0 :=
  sorry

theorem one_shot :
  get_chance 1 1 1 = 0 ∧ get_chance 1 0 1 = 1 :=
  sorry
-- </vc-theorems>