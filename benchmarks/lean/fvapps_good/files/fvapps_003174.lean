-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sharkovsky (a b : Nat) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sharkovsky_reflexive {a : Nat} :
  ¬ sharkovsky a a := 
  sorry

theorem sharkovsky_antisymmetric {a b : Nat} :
  a ≠ b → ¬(sharkovsky a b ∧ sharkovsky b a) :=
  sorry

theorem sharkovsky_transitive {a b c : Nat} :
  sharkovsky a b → sharkovsky b c → sharkovsky a c :=
  sorry

theorem odd_precedes_power_of_two {a : Nat} (h : a ≥ 3) (h2 : a % 2 = 1) :
  sharkovsky a (2^4) :=
  sorry
-- </vc-theorems>