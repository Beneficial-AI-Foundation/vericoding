-- <vc-preamble>
def isSorted (xs : List Nat) : Prop :=
  ∀ i j, i < j → j < List.length xs → xs[i]! < xs[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def extra_perfect (n : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem extra_perfect_only_odd {n : Nat} :
  ∀ x, x ∈ extra_perfect n → x % 2 = 1 :=
sorry

theorem extra_perfect_bounded {n : Nat} :
  ∀ x, x ∈ extra_perfect n → x ≤ n :=
sorry

theorem extra_perfect_length {n : Nat} :
  List.length (extra_perfect n) = (n + 1) / 2 :=
sorry

theorem extra_perfect_binary_ones {n : Nat} :
  ∀ x, x ∈ extra_perfect n →
    ((x &&& 1) = 1) ∧
    ((x &&& (1 <<< (Nat.log2 x))) = (1 <<< (Nat.log2 x))) :=
sorry
-- </vc-theorems>