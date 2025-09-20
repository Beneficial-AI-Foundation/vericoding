-- <vc-preamble>
def sumList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + sumList xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toBase (num base : Nat) : String :=
  sorry

def sumItUp (nums : List (String × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_it_up_equals_decimal_sum {nums : List (Nat × Nat)} :
  ∀ pairs : List (String × Nat),
  (∀ p : String × Nat, p ∈ pairs →
    ∃ n ∈ nums, p.1 = toBase n.1 p.2) →
  sumItUp pairs = sumList (nums.map Prod.fst) :=
sorry

theorem sum_it_up_empty : sumItUp [] = 0 :=
sorry

theorem sum_it_up_single {n : String} {b : Nat} :
  b ≥ 2 → b ≤ 36 →
  ∃ k : Nat, sumItUp [(n, b)] = k :=
sorry

theorem base_conversion_roundtrip {n : Nat} {b : Nat} :
  n ≤ 1000000 → b ≥ 2 → b ≤ 36 →
  ∃ k : Nat, k = n ∧ String.toNat! (toBase n b) = k :=
sorry
-- </vc-theorems>