def max_race_wins (n : Nat) (my_times : List Nat) (opp_times: List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isDescending (l : List Nat) : Prop :=
  ∀ i j, i < l.length → j < l.length → i < j → 
    match l.get? i, l.get? j with
    | some x, some y => x ≥ y
    | _, _ => True

theorem max_race_wins_result_bounds {n : Nat} {my_times opp_times : List Nat} 
  (h1 : n > 0) (h2 : n ≤ 100)
  (h3 : ∀ x ∈ my_times, 1 ≤ x ∧ x ≤ 1000)
  (h4 : ∀ x ∈ opp_times, 1 ≤ x ∧ x ≤ 1000) :
  let result := max_race_wins n my_times opp_times
  0 ≤ result ∧ result ≤ n :=
sorry

theorem max_race_wins_length {n : Nat} {my_times opp_times my_times_out opp_times_out : List Nat}
  (h1 : n > 0)
  (h2 : my_times_out.length = n)
  (h3 : opp_times_out.length = n)
  (h4 : max_race_wins n my_times opp_times > 0) : True :=
sorry

theorem max_race_wins_sorted {n : Nat} {my_times opp_times my_times_out opp_times_out : List Nat}
  (h1 : max_race_wins n my_times opp_times > 0) 
  (h2 : isDescending my_times_out)
  (h3 : isDescending opp_times_out) : True :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_race_wins 3 [5, 4, 1] [5, 4, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_race_wins 2 [3, 1] [2, 2]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_race_wins 4 [5, 4, 3, 2] [6, 5, 4, 1]

-- Apps difficulty: interview
-- Assurance level: guarded