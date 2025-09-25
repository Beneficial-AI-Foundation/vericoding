-- <vc-preamble>
def List.sum (xs : List Nat) : Nat := 
  sorry

def max_subsequences (n : Nat) (arr : List Int) : List (List Nat) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_result (n : Nat) (result : List (List Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_subsequences_valid {n : Nat} {arr : List Int} 
  (h1 : n > 0) 
  (h2 : n = arr.length)
  (h3 : ∀ x ∈ arr, -1000 ≤ x ∧ x ≤ 1000)
  (h4 : ∀ (i : Fin arr.length) (j : Fin arr.length), i ≠ j → arr[i] ≠ arr[j]) :
  is_valid_result n (max_subsequences n arr) := by
  sorry

theorem max_subsequences_bounds {n : Nat} {arr : List Int} 
  (h1 : n > 0)
  (h2 : n = arr.length)
  (h3 : ∀ x ∈ arr, -1000 ≤ x ∧ x ≤ 1000)
  (h4 : ∀ (i : Fin arr.length) (j : Fin arr.length), i ≠ j → arr[i] ≠ arr[j]) :
  let result := max_subsequences n arr
  1 ≤ result.head!.head! ∧ result.head!.head! ≤ n := by
  sorry

theorem max_subsequences_sum {n : Nat} {arr : List Int}
  (h1 : n > 0)
  (h2 : n = arr.length)
  (h3 : ∀ x ∈ arr, -1000 ≤ x ∧ x ≤ 1000)
  (h4 : ∀ (i : Fin arr.length) (j : Fin arr.length), i ≠ j → arr[i] ≠ arr[j]) :
  let result := max_subsequences n arr
  List.sum (result.tail.map (λ subseq => subseq.head!)) = n := by
  sorry

theorem max_subsequences_lengths {n : Nat} {arr : List Int}
  (h1 : n > 0)
  (h2 : n = arr.length) 
  (h3 : ∀ x ∈ arr, -1000 ≤ x ∧ x ≤ 1000)
  (h4 : ∀ (i : Fin arr.length) (j : Fin arr.length), i ≠ j → arr[i] ≠ arr[j]) :
  let result := max_subsequences n arr
  ∀ subseq ∈ result.tail, subseq.head! ≥ 1 := by
  sorry

/-
info: list(range(1, n1 + 1))
-/
-- #guard_msgs in
-- #eval sorted sum([x[1:] for x in result1[1:]], [])

/-
info: 7
-/
-- #guard_msgs in
-- #eval len result2[1]

/-
info: list(range(1, n2 + 1))
-/
-- #guard_msgs in
-- #eval sorted result2[1][1:]

/-
info: list(range(1, n3 + 1))
-/
-- #guard_msgs in
-- #eval sorted sum([x[1:] for x in result3[1:]], [])
-- </vc-theorems>