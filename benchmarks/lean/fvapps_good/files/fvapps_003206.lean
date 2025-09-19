-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PowerPair := List Nat 

def compare_powers (p1 p2 : PowerPair) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compare_powers_valid_result (n1 n2 : PowerPair) : 
  let r := compare_powers n1 n2
  r = -1 ∨ r = 0 ∨ r = 1 :=
sorry

theorem compare_powers_reflexive (n : PowerPair) :
  compare_powers n n = 0 :=
sorry

theorem compare_powers_antisymmetric (n1 n2 : PowerPair) :
  compare_powers n1 n2 = -(compare_powers n2 n1) :=
sorry

theorem compare_powers_transitive_positive (x y z : PowerPair) : 
  compare_powers x y = 1 → compare_powers y z = 1 → compare_powers x z = 1 :=
sorry

theorem compare_powers_transitive_negative (x y z : PowerPair) :
  compare_powers x y = -1 → compare_powers y z = -1 → compare_powers x z = -1 :=
sorry
-- </vc-theorems>