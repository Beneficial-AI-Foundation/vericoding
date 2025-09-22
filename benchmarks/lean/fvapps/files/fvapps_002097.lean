-- <vc-preamble>
def sumList (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h::t => h + sumList t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_thomas_rank (n : Nat) (scores : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem thomas_rank_in_range {n : Nat} {scores : List (List Nat)} 
  (h1 : n > 0) 
  (h2 : scores.length = n)
  (h3 : ∀ s ∈ scores, s.length = 4)
  (h4 : ∀ s ∈ scores, ∀ x ∈ s, x ≤ 100) :
  let rank := find_thomas_rank n scores
  1 ≤ rank ∧ rank ≤ n :=
sorry

theorem thomas_rank_counts_better_scores {n : Nat} {scores : List (List Nat)}
  (h1 : n > 0)
  (h2 : scores.length = n) 
  (h3 : ∀ s ∈ scores, s.length = 4)
  (h4 : ∀ s ∈ scores, ∀ x ∈ s, x ≤ 100) :
  let rank := find_thomas_rank n scores
  let thomas_total := sumList scores.head!
  let better_scores := (scores.tail.filter (fun s => sumList s > thomas_total)).length
  better_scores = rank - 1 :=
sorry

theorem equal_scores_gives_first {n : Nat} {score : Nat} {scores : List (List Nat)}
  (h1 : n > 0)
  (h2 : score ≤ 100)
  (h3 : scores = List.replicate n (List.replicate 4 score)) :
  find_thomas_rank n scores = 1 :=
sorry

theorem single_student_first :
  find_thomas_rank 1 [[0,0,0,0]] = 1 :=
sorry

theorem lowest_score_gives_last :
  find_thomas_rank 3 [[0,0,0,0], [100,100,100,100], [100,100,100,100]] = 3 :=
sorry
-- </vc-theorems>