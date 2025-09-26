-- <vc-preamble>
def maxList (l : List Nat) : Float :=
  Float.ofNat (l.foldl max 0)

def listXor (l : List Nat) : Float :=
  Float.ofNat (l.foldl Nat.xor 0)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_expected_beauty (n : Nat) (beauties : List Nat) (probs : List Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expected_beauty_bounds {n : Nat} {beauties : List Nat} {probs : List Float}
    (h1 : beauties.length = n)
    (h2 : probs.length = n)
    (h3 : ∀ p ∈ probs, 0 ≤ p ∧ p ≤ 1)
    (h4 : beauties.length > 0)
    : 0 ≤ calculate_expected_beauty n beauties probs ∧
      calculate_expected_beauty n beauties probs ≤ maxList beauties :=
sorry

theorem probabilities_zero_one {n : Nat} {beauties : List Nat}
    (h1 : beauties.length = n)
    : calculate_expected_beauty n beauties (List.replicate n 0) = 0 ∧
      calculate_expected_beauty n beauties (List.replicate n 1) =
        listXor beauties :=
sorry

theorem symmetry {n : Nat} {beauties : List Nat} {probs : List Float}
    (h1 : beauties.length = n)
    (h2 : probs.length = n)
    (σ : List.Perm beauties (beauties.take n))
    (τ : List.Perm probs (probs.take n))
    : calculate_expected_beauty n beauties probs =
      calculate_expected_beauty n (beauties.take n) (probs.take n) :=
sorry
-- </vc-theorems>