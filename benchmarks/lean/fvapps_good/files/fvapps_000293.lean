-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def least_ops_express_target (x : Nat) (target : Nat) : Nat := sorry

theorem output_is_non_negative
  (x : Nat) (target : Nat)
  (h1 : x ≥ 2) (h2 : x ≤ 100)
  (h3 : target ≥ 1) (h4 : target ≤ 1000000) :
  least_ops_express_target x target ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem target_equals_x_minimal_ops
  (x : Nat)
  (h1 : x ≥ 2) (h2 : x ≤ 100) :
  least_ops_express_target x x ≤ 2 := sorry

theorem power_requires_fewer_ops
  (x power : Nat)
  (h1 : x ≥ 2) (h2 : x ≤ 20)
  (h3 : power ≥ 2) (h4 : power ≤ 5) :
  least_ops_express_target x (x^power) ≤ least_ops_express_target x (x^power + 1) := sorry
-- </vc-theorems>