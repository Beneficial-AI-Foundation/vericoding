-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Submission := Nat × Nat

def get_total_score (submissions : List Submission) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_score_nonnegative
  (submissions: List Submission) :
  get_total_score submissions ≥ 0 :=
sorry

theorem total_score_bounded
  (submissions: List Submission) :
  get_total_score submissions ≤ 800 :=
sorry

theorem total_score_idempotent
  (submissions: List Submission) :
  get_total_score submissions = get_total_score (submissions ++ submissions) :=
sorry

theorem total_score_only_first_eight
  (submissions: List Submission) :
  get_total_score submissions = 
  get_total_score (submissions.filter (fun s => s.fst ≤ 8)) :=
sorry

theorem high_problem_numbers_zero
  (submissions: List Submission)
  (h: ∀ s ∈ submissions, s.fst ≥ 9) :
  get_total_score submissions = 0 :=
sorry
-- </vc-theorems>