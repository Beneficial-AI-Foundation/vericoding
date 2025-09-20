-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSubsequence (smaller larger : String) : Bool :=
  sorry

def solve (n : Nat) (k : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_properties {n k : Nat} (h : k < (ToString.toString n).length) :
  let result := solve n k
  (result.length = (ToString.toString n).length - k) ∧
  (isSubsequence result (ToString.toString n) = true) ∧
  (result.toNat! ≤ n) :=
sorry

theorem remove_zero_digits (n : Nat) :
  solve n 0 = ToString.toString n :=
sorry

theorem result_is_minimal {n k : Nat} (h1 : n ≥ 10) (h2 : k ≥ 1) (h3 : k < (ToString.toString n).length) :
  let result := solve n k
  ∀ (s : String),
    isSubsequence s (ToString.toString n) = true →
    s.length = (ToString.toString n).length - k →
    result.toNat! ≤ s.toNat! :=
sorry
-- </vc-theorems>