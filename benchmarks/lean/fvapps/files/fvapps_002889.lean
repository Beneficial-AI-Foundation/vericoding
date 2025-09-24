-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfDigits (n : Nat) : Nat :=
  sorry

def rthn_between (a b : Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rthn_between_ordered_bounds {a b : Int} (h : a ≤ b) (h₁ : 0 ≤ a) (h₂ : b ≤ 10000) :
  let result := rthn_between a b

  (∀ i j, i < j → i < List.length result → j < List.length result →
    result[i]! ≤ result[j]!) ∧

  (∀ x ∈ result, a ≤ x ∧ x ≤ b) ∧

  (∀ x ∈ result, x % sumOfDigits (Int.toNat x) = 0) :=
sorry

theorem rthn_between_same_bounds {n : Int} (h : 0 ≤ n) (h₁ : n ≤ 10000) :
  let result := rthn_between n n
  (result ≠ [] →
    List.length result = 1 ∧
    result[0]! = n ∧
    n % sumOfDigits (Int.toNat n) = 0) :=
sorry

theorem rthn_between_inverted_bounds {n : Int} (h : 0 ≤ n) (h₁ : n ≤ 10000) :
  rthn_between n (n-1) = [] :=
sorry

theorem rthn_between_edge_cases :
  (rthn_between 0 0 = []) ∧
  (rthn_between (-1) 10 = [10]) :=
sorry
-- </vc-theorems>