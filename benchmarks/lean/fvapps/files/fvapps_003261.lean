-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bin_mul (m n : Nat) : List Nat := sorry

def list_sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + list_sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem bin_mul_elements_natural (m n : Nat) :
  ∀ x, x ∈ bin_mul m n → x ≥ 0 := sorry

theorem bin_mul_zero_empty (n : Nat) :
  bin_mul n 0 = [] ∧ bin_mul 0 n = [] := sorry

theorem bin_mul_commutative (m n : Nat) :
  bin_mul m n = bin_mul n m := sorry
-- </vc-theorems>