-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_wheel_of_fortune (n : Nat) (wheel : List Nat) (queries : List Nat) : List Nat := sorry

theorem results_length_matches_queries_length
  (n : Nat) (wheel : List Nat) (queries : List Nat) :
  List.length (solve_wheel_of_fortune n wheel queries) = List.length queries := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem results_are_bounded 
  (n : Nat) (wheel : List Nat) (queries : List Nat) :
  ∀ x ∈ solve_wheel_of_fortune n wheel queries, 
  1 ≤ x ∧ x ≤ n :=
  sorry

theorem single_occurrence_gives_n
  (n : Nat) (wheel : List Nat) (queries : List Nat) :
  ∀ (q : Nat) (i : Fin (List.length queries)),
  queries.get i = q →
  List.count q wheel = 1 →
  (solve_wheel_of_fortune n wheel queries).get ⟨i.1, by
    rw [results_length_matches_queries_length]
    exact i.2⟩ = n :=
  sorry

theorem multiple_occurrences_bound
  (n : Nat) (wheel : List Nat) (queries : List Nat) :
  ∀ (q : Nat) (i : Fin (List.length queries)),
  queries.get i = q →
  List.count q wheel ≥ 2 →
  (solve_wheel_of_fortune n wheel queries).get ⟨i.1, by 
    rw [results_length_matches_queries_length]
    exact i.2⟩ ≤ n / 2 :=
  sorry

theorem identical_wheel_gives_ones
  (n : Nat) :
  solve_wheel_of_fortune n (List.replicate n 1) [1] = [1] :=
  sorry
-- </vc-theorems>