-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lcm : List Nat → Nat
| [] => 1 
| _  => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lcm_self_identity (n : Nat) : n > 0 → lcm [n, n] = n := by
  sorry

theorem lcm_commutative (a b : Nat) : a > 0 → b > 0 → lcm [a, b] = lcm [b, a] := by
  sorry 

theorem lcm_divides (a b : Nat) : a > 0 → b > 0 → 
  (lcm [a, b] % a = 0 ∧ lcm [a, b] % b = 0) := by
  sorry

theorem lcm_empty : lcm [] = 1 := by
  sorry

theorem lcm_associative (a b c : Nat) : a > 0 → b > 0 → c > 0 →
  lcm [a, lcm [b, c]] = lcm [lcm [a, b], c] := by
  sorry

theorem lcm_minimum_bound {n : Nat} (nums : List Nat) :
  (∀ x ∈ nums, x > 0) → n ∈ nums → lcm nums ≥ n := by
  sorry
-- </vc-theorems>