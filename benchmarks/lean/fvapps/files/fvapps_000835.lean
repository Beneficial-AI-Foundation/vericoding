-- <vc-preamble>
def isDescending (l : List Nat) : Prop :=
  ∀ i j, i < l.length → j < l.length → i < j →
    match l.get? i, l.get? j with
    | some x, some y => x ≥ y
    | _, _ => True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_race_wins (n : Nat) (my_times : List Nat) (opp_times: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>