-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kthFactor (n : Nat) (k : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_factor_always_one (n : Nat) (h : n > 0) :
  kthFactor n 1 = 1 := sorry

theorem k_greater_than_total_factors_negative_one (n k : Nat) (h₁ : n > 0) (h₂ : k > 0) :
  let numFactors := (List.range n).filter (fun i => n % (i+1) = 0) |>.length
  k > numFactors → kthFactor n k = -1 := sorry

theorem valid_factor_divides_evenly (n k : Nat) (h₁ : n > 0) (h₂ : k > 0) :
  kthFactor n k ≠ -1 → n % (kthFactor n k).toNat = 0 := sorry

theorem factors_are_ordered (n k : Nat) (h₁ : n > 0) (h₂ : k > 0) :
  kthFactor n k ≠ -1 →
  ((List.range (kthFactor n k).toNat).filter (fun i => n % (i+1) = 0)).length = k - 1 := sorry
-- </vc-theorems>