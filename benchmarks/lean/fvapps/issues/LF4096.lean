-- <vc-preamble>
def greek_index (l : GreekLetter) : Nat :=
  match l with
  | .alpha => 0 | .beta => 1 | .gamma => 2 | .delta => 3
  | .epsilon => 4 | .zeta => 5 | .eta => 6 | .theta => 7
  | .iota => 8 | .kappa => 9 | .lambda => 10 | .mu => 11
  | .nu => 12 | .xi => 13 | .omicron => 14 | .pi => 15
  | .rho => 16 | .sigma => 17 | .tau => 18 | .upsilon => 19
  | .phi => 20 | .chi => 21 | .psi => 22 | .omega => 23
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greek_comparator (a b : GreekLetter) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greek_comparator_reflexive (a : GreekLetter) : 
  greek_comparator a a = 0 :=
sorry

theorem greek_comparator_antisymmetric (a b : GreekLetter) :
  greek_comparator a b = -(greek_comparator b a) :=
sorry 

theorem greek_comparator_transitive (a b c : GreekLetter) :
  greek_comparator a b > 0 → greek_comparator b c > 0 → greek_comparator a c > 0 :=
sorry

theorem greek_comparator_position {a b : GreekLetter} :
  a = b → greek_comparator a b = 0 :=
sorry

theorem greek_comparator_order {a b : GreekLetter} :
  greek_index a < greek_index b → greek_comparator a b < 0 :=
sorry

theorem greek_comparator_order_reverse {a b : GreekLetter} :
  greek_index a > greek_index b → greek_comparator a b > 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval greek_comparator "chi" "chi"
-- </vc-theorems>