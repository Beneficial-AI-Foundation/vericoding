-- <vc-preamble>
def List.sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort (lt : α → α → Bool) (l : List α) : List α := sorry

def max_quest_interest (n : Nat) (T : Nat) (tasks : List (Nat × Nat)) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_quest_interest_non_negative (n T : Nat) (tasks : List (Nat × Nat)) :
  max_quest_interest n T tasks ≥ 0 := sorry

theorem max_quest_interest_bounded_by_sum (n T : Nat) (tasks : List (Nat × Nat)) :
  let interest_values := tasks.map (fun p => p.2)
  max_quest_interest n T tasks ≤ interest_values.sum := sorry

theorem max_quest_interest_time_constraint (n T : Nat) (tasks : List (Nat × Nat)) :
  let max_possible := min n (2^T)
  let interest_values := tasks.map (fun p => p.2)
  let sorted_interests := interest_values.sort (fun a b => b ≤ a)
  let max_interests := sorted_interests.take max_possible
  max_quest_interest n T tasks ≤ max_interests.sum := sorry

theorem same_time_tasks_property (n T : Nat) (tasks : List (Nat × Nat)) 
    (h : ∀ t ∈ tasks.map Prod.fst, t = 1) :
  let interest_values := tasks.map (fun p => p.2)
  let sorted_interests := interest_values.sort (fun a b => b ≤ a)
  let feasible_interests := sorted_interests.take (2^(T-1))
  max_quest_interest n T tasks ≤ feasible_interests.sum := sorry

theorem small_time_constraint_property (n T : Nat) (tasks : List (Nat × Nat)) (h : T ≤ 4) :
  let max_quests := 2^(T-1)
  let interest_values := tasks.map (fun p => p.2)
  let sorted_interests := interest_values.sort (fun a b => b ≤ a)
  let max_interests := sorted_interests.take max_quests
  max_quest_interest n T tasks ≤ max_interests.sum := sorry

/-
info: 11
-/
-- #guard_msgs in
-- #eval max_quest_interest 5 5 [(1, 1), (1, 1), (2, 2), (3, 3), (4, 4)]

/-
info: 9
-/
-- #guard_msgs in
-- #eval max_quest_interest 5 5 [(4, 1), (4, 2), (4, 3), (4, 4), (4, 5)]

/-
info: 10
-/
-- #guard_msgs in
-- #eval max_quest_interest 2 2 [(1, 1), (2, 10)]
-- </vc-theorems>