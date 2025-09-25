-- <vc-preamble>
def find_max_score (N : Nat) (K : Nat) (A : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_int (a b : Int) : Int :=
  if a ≥ b then a else b
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_score_k_bounds {A : List Int} {K : Nat} {N : Nat} 
  (h1 : A.length = N)
  (h2 : N > 0)
  (h3 : K ≤ N)
  (h4 : ∀ x ∈ A, -1000 ≤ x ∧ x ≤ 1000) :
  let result := find_max_score N K A
  let sorted_tail := List.take K (List.reverse (List.mergeSort (. ≤ .) A))
  let sorted_suffix_sum := List.foldl (· + ·) 0 sorted_tail
  let positive_sum := List.foldl (· + ·) 0 (List.filter (λ x => x > 0) A)
  sorted_suffix_sum ≤ result ∧ result ≤ positive_sum :=
  sorry

theorem find_max_score_k_equals_n {A : List Int} {N : Nat}
  (h1 : A.length = N)
  (h2 : N > 0)
  (h3 : ∀ x ∈ A, -1000 ≤ x ∧ x ≤ 1000) :
  find_max_score N N A = List.foldl (· + ·) 0 A :=
  sorry

theorem find_max_score_all_positive {A : List Int} {N : Nat}
  (h1 : A.length = N)
  (h2 : N > 0)
  (h3 : ∀ x ∈ A, 0 ≤ x ∧ x ≤ 1000) :
  let K := if N > 1 then N / 2 else 1
  find_max_score N K A = List.foldl (· + ·) 0 A :=
  sorry

theorem find_max_score_all_negative {A : List Int} {N : Nat}
  (h1 : A.length = N)
  (h2 : N > 0)
  (h3 : ∀ x ∈ A, -1000 ≤ x ∧ x < 0) :
  let K := if N > 1 then N / 2 else 1
  let sliding_sums := List.range (N - K + 1) |>.map (λ i => List.foldl (· + ·) 0 (List.take K (List.drop i A)))
  find_max_score N K A = sliding_sums.foldl max_int (sliding_sums.head!) :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_max_score 5 2 [5, 3, -2, 1, 1]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_max_score 5 2 [1, 2, 3, -1, -2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_max_score 3 1 [3, 2, 1]
-- </vc-theorems>