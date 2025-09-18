-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def survivor (nums : List Nat) : Int := sorry

theorem survivor_result_constraint (nums : List Nat) :
  let result := survivor nums
  result = -1 ∨ result = 0 ∨ result > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem survivor_empty_list :
  survivor [] = -1 := sorry

theorem survivor_contains_one (nums : List Nat) :
  nums.contains 1 → survivor nums = 0 := sorry

private def listGcd : List Nat → Nat := sorry

theorem survivor_gcd (nums : List Nat) :
  nums ≠ [] → listGcd nums > 1 → survivor nums = -1 := sorry

private def listProd : List Nat → Nat := sorry

theorem survivor_product_bound (nums : List Nat) :
  let result := survivor nums
  result ≥ 0 → nums ≠ [] → result < listProd nums := sorry

theorem survivor_singleton (n : Nat) :
  n > 0 → survivor [n] = (if n = 1 then 0 else -1) := sorry

theorem survivor_coprime_pair (n : Nat) :
  n ≥ 2 →
  let result := survivor [n, n+1]
  result ≥ 0 ∧ result < n * (n+1) := sorry
-- </vc-theorems>