-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_gcd_prob (n : Nat) : String := sorry

theorem calc_gcd_prob_fraction_format (n : Nat) 
    (h : n > 0) (h2 : n ≤ 1000) :
    let result := calc_gcd_prob n
    let nums := result.splitOn "/"
    let num := String.toNat! (nums.get! 0)
    let denom := String.toNat! (nums.get! 1)
    denom > 0 ∧ Nat.gcd num denom = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_gcd_prob_probability_range (n : Nat)
    (h : n > 0) (h2 : n ≤ 1000) :
    let result := calc_gcd_prob n
    let nums := result.splitOn "/"
    let num := String.toNat! (nums.get! 0) 
    let denom := String.toNat! (nums.get! 1)
    num / denom ≥ 0 ∧ num / denom ≤ 1 := sorry
-- </vc-theorems>