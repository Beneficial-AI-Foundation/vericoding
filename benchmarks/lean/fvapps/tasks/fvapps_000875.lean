-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def count_signs_with_two_digits (k: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_signs_always_positive (k: Nat) (hk: k ≥ 1) (hk': k ≤ 1000):
  count_signs_with_two_digits k > 0 :=
  sorry

theorem count_signs_mod_property (k: Nat) (hk: k ≥ 1) (hk': k ≤ 1000):
  count_signs_with_two_digits k ≥ 0 ∧ count_signs_with_two_digits k < MOD :=
  sorry

theorem count_signs_doubles_each_k (k: Nat) (hk: k ≥ 1) (hk': k ≤ 10):
  count_signs_with_two_digits (k + 1) = ((count_signs_with_two_digits k) * 2) % MOD :=
  sorry
-- </vc-theorems>