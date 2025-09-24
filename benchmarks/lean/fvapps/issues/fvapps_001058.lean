-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs => x + List.sum xs

def List.sortBy (lt : α → α → Bool) (xs : List α) : List α :=
match xs with
| [] => []
| [x] => [x]
| x::xs => x::xs -- stub implementation to avoid termination issues
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_min_score (n k e m : Nat) (other_scores : List (List Nat)) (sergey_scores : List Nat) : Nat ⊕ Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_score_bounded {n k e m : Nat} {other_scores : List (List Nat)} {sergey_scores : List Nat}
  (h1 : n ≥ 2)
  (h2 : k < n)
  (h3 : k ≥ 1) 
  (h4 : e ≥ 2)
  (h5 : m ≥ 1)
  (h6 : calculate_min_score n k e m other_scores sergey_scores = .inl score)
  : 0 ≤ score ∧ score ≤ m :=
sorry

theorem min_score_achieves_position {n k e m : Nat} {other_scores : List (List Nat)} {sergey_scores : List Nat}
  (h1 : n ≥ 2)
  (h2 : k < n)
  (h3 : k ≥ 1)
  (h4 : e ≥ 2)
  (h5 : m ≥ 1)
  (h6 : calculate_min_score n k e m other_scores sergey_scores = .inl score)
  : let sergey_total := score + List.sum sergey_scores
    let other_totals := (other_scores.map List.sum).sortBy (fun x y => x > y)
    List.length (other_totals.filter (fun x => x > sergey_total)) < k :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval calculate_min_score 4 2 3 10 [[7, 7, 7], [4, 6, 10], [7, 10, 9]] [9, 9]

/-
info: 'Impossible'
-/
-- #guard_msgs in
-- #eval calculate_min_score 3 1 2 5 [[5, 5], [5, 5]] [0]

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_min_score 3 2 2 10 [[5, 1], [1, 1]] [10]
-- </vc-theorems>