-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_grading_thresholds (n : Nat) (scores : List Nat) : String := sorry

theorem valid_score_thresholds (n : Nat) (scores : List Nat)
  (h_n : n ∈ [4, 8, 12, 16, 20])
  (h_scores : ∀ x ∈ scores, x ≤ 100)
  (h_length : scores.length = n)
  (h_unique : ∀ i j, i < scores.length → j < scores.length → i ≠ j → scores.get! i ≠ scores.get! j) :
  let result := solve_grading_thresholds n scores 
  if result ≠ "-1" then ∃ a b c : Nat,
    a < b ∧ b < c ∧
    a = (scores.toArray.qsort (· ≤ ·)).toList.get! (n/4) ∧
    b = (scores.toArray.qsort (· ≤ ·)).toList.get! (2*n/4) ∧  
    c = (scores.toArray.qsort (· ≤ ·)).toList.get! (3*n/4)
  else True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem duplicate_scores_invalid (n : Nat) (base_score : Nat)
  (h_n : n ∈ [4, 8, 12, 16])
  (h_base : base_score ≤ 100) :
  let scores := List.range n |>.map (λ i => base_score + i)
  let dup_val := scores.get! ((n/4)-1)
  let scores_with_dup := scores.take (n/4) ++ [dup_val] ++ scores.drop (n/4 + 1)
  solve_grading_thresholds n scores_with_dup = "-1" := sorry
-- </vc-theorems>