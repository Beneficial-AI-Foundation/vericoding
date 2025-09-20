-- <vc-preamble>
def name_of_mystery : String :=
  "Gray code"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mystery (n : Nat) : Nat :=
  sorry

def mystery_inv (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mystery_inverse : ∀ n : Nat, n < 2^32 →
  mystery (mystery_inv n) = n ∧ mystery_inv (mystery n) = n :=
sorry

theorem mystery_preserves_non_negative : ∀ n : Nat,
  mystery n ≥ 0 ∧ mystery_inv n ≥ 0 :=
sorry

theorem mystery_bit_length : ∀ n : Nat, n < 2^16 →
  n.log2 - (mystery n).log2 ≤ 1 ∧
  n.log2 - (mystery_inv n).log2 ≤ 1 :=
sorry

theorem mystery_name_is_gray_code :
  name_of_mystery = "Gray code" :=
sorry
-- </vc-theorems>