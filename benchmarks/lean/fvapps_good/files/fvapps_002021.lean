-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_inversions (n : Nat) (arr : List Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_inversions_output_nat (n : Nat) (arr : List Nat) :
  let (inv, out) := solve_inversions n arr
  Nat.zero ≤ inv ∧ Nat.zero ≤ out :=
  sorry

theorem solve_inversions_deterministic (n : Nat) (arr : List Nat) :
  let res1 := solve_inversions n arr
  let res2 := solve_inversions n arr
  res1 = res2 :=
  sorry

structure Sorted (l : List Nat) : Prop where
  sorted : ∀ i j, i < j → j < l.length → 
    match l.get? i, l.get? j with
    | some x, some y => x ≤ y
    | _, _ => True

theorem sorted_array_zero_inversions (n : Nat) (arr sorted : List Nat) :
  Sorted sorted →
  List.length sorted = n →
  let (inv, _) := solve_inversions n sorted
  inv = 0 :=
  sorry
-- </vc-theorems>