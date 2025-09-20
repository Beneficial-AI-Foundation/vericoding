-- <vc-preamble>
def abs (n : Nat) (m : Nat) : Nat :=
  if n ≥ m then n - m else m - n

def isSortedList : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => x ≤ y && isSortedList (y :: xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_sum_permutation (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_length {n : Nat} (h : 0 < n) (h2 : n ≤ 1000) :
  let result := find_min_sum_permutation n
  List.length result = n ∧
  isSortedList result :=
sorry

theorem sum_property {n : Nat} (h : 0 < n) (h2 : n ≤ 1000) :
  let result := find_min_sum_permutation n
  let pairs := List.zip (List.take (List.length result - 1) result) (List.drop 1 result)
  let cumsum := List.foldl (fun acc (p : Nat × Nat) => acc + abs p.1 p.2) 0 pairs
  let rev := List.reverse result
  let rev_pairs := List.zip (List.take (List.length rev - 1) rev) (List.drop 1 rev)
  let rev_sum := List.foldl (fun acc (p : Nat × Nat) => acc + abs p.1 p.2) 0 rev_pairs
  cumsum ≤ rev_sum :=
sorry
-- </vc-theorems>