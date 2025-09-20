-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_contiguous_subsequence (N Q K : Nat) (A : List Nat) (S : String) : List Nat :=
sorry

def count_max_consecutive_ones (A : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_length_matches_question_marks {N Q K : Nat} {A : List Nat} {S : String}
  (h1 : N > 0) (h2 : Q > 0) (h3 : K > 0)
  (h4 : ∀ x ∈ A, x ≤ 1) :
  (longest_contiguous_subsequence N Q K A S).length =
    (S.data.filter (. = '?')).length :=
sorry

theorem results_bounded_by_k {N Q K : Nat} {A : List Nat} {S : String}
  (h1 : N > 0) (h2 : Q > 0) (h3 : K > 0)
  (h4 : ∀ x ∈ A, x ≤ 1) :
  ∀ x ∈ (longest_contiguous_subsequence N Q K A S), x ≤ K :=
sorry

theorem results_non_negative {N Q K : Nat} {A : List Nat} {S : String}
  (h1 : N > 0) (h2 : Q > 0) (h3 : K > 0)
  (h4 : ∀ x ∈ A, x ≤ 1) :
  ∀ x ∈ (longest_contiguous_subsequence N Q K A S), x ≥ 0 :=
sorry

theorem zero_array_gives_zero_result {N Q K : Nat} {A : List Nat} {S : String}
  (h1 : N > 0) (h2 : Q > 0) (h3 : K > 0)
  (h4 : ∀ x ∈ A, x = 0) :
  ∀ x ∈ (longest_contiguous_subsequence N Q K A S), x = 0 :=
sorry

theorem single_question_mark_result {N K : Nat} {A : List Nat}
  (h1 : N > 0) (h2 : K > 0)
  (h3 : ∀ x ∈ A, x ≤ 1)
  (h4 : (longest_contiguous_subsequence N 1 K A "?").length > 0) :
  (longest_contiguous_subsequence N 1 K A "?")[0]! = min (count_max_consecutive_ones A) K :=
sorry
-- </vc-theorems>