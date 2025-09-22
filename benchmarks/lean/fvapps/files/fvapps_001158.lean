-- <vc-preamble>
def count_divisible (k : Nat) (A : List Nat) : Nat :=
  List.foldl (fun acc x => if k % x = 0 then acc + 1 else acc) 0 A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_gcd (lst : List Nat) : Nat := sorry

def solve_contiguous_generators (N : Nat) (A : List Nat) (queries : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_length_matches_queries
  {N : Nat} {A : List Nat} {queries : List Nat} :
  List.length (solve_contiguous_generators N A queries) = List.length queries :=
sorry

theorem all_results_nonnegative
  {N : Nat} {A : List Nat} {queries : List Nat} :
  ∀ x ∈ solve_contiguous_generators N A queries, x ≥ 0 :=
sorry

theorem result_geq_min_divisible_count
  {N : Nat} {A : List Nat} {queries : List Nat}
  (i : Nat) (k : Nat) (h₁ : i < List.length queries) :
  let divisible_count := count_divisible k A
  let result := solve_contiguous_generators N A queries
  result.get! i ≥ min divisible_count N :=
sorry

theorem single_element_generates_self
  {N : Nat} {A : List Nat} :
  ∀ x ∈ solve_contiguous_generators N A A, x ≥ 1 :=
sorry

theorem gcd_subsequence_property
  {N : Nat} {A : List Nat} {K : Nat}
  (i j : Nat) (h₁ : i ≤ j) (h₂ : j < N) :
  let subseq := A.take (j+1) |>.drop i
  let subseq_gcd := list_gcd subseq
  K % subseq_gcd = 0 →
  (solve_contiguous_generators N A [K]).get! 0 ≥ 1 :=
sorry
-- </vc-theorems>