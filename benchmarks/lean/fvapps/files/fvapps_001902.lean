-- <vc-preamble>
def listContains (l : List Nat) (n : Nat) : Prop :=
  n ∈ l
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countOnes (n : Nat) : Nat :=
  sorry

def circularPermutation (n : Nat) (start : Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem circularPermutation_length (n : Nat) (start : Nat)
  (h : start < 2^n) :
  (circularPermutation n start).length = 2^n :=
sorry

theorem circularPermutation_starts_with_start (n : Nat) (start : Nat)
  (h : start < 2^n) :
  (circularPermutation n start).head! = start :=
sorry

theorem circularPermutation_contains_all_numbers (n : Nat) (start : Nat)
  (h : start < 2^n) (k : Nat) (hk : k < 2^n):
  listContains (circularPermutation n start) k :=
sorry

theorem circularPermutation_adjacent_differ_by_one_bit (n : Nat) (start : Nat)
  (h : start < 2^n) (i : Nat) (h2 : i < (circularPermutation n start).length - 1) :
  countOnes ((circularPermutation n start)[i]! ^^^ (circularPermutation n start)[i+1]!) = 1 :=
sorry

theorem circularPermutation_first_last_differ_by_one_bit (n : Nat) (start : Nat)
  (h : start < 2^n) :
  countOnes ((circularPermutation n start).head! ^^^ (circularPermutation n start).getLast!) = 1 :=
sorry

theorem circularPermutation_invalid_start (n : Nat) (start : Nat)
  (h : start ≥ 2^n) :
  circularPermutation n start = [] :=
sorry
-- </vc-theorems>