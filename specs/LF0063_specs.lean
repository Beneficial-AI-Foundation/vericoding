-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cars_meeting (n l : Nat) (flags : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem meeting_time_positive (n l : Nat) (flags : List Nat) 
  (h1 : n > 0) (h2 : l > n) (h3 : flags.length = n) :
  solve_cars_meeting n l flags > 0 :=
  sorry

theorem meeting_time_less_than_length (n l : Nat) (flags : List Nat)
  (h1 : n > 0) (h2 : l > n) (h3 : flags.length = n) :
  solve_cars_meeting n l flags < l :=
  sorry

theorem meeting_time_less_than_half (n l : Nat) (flags : List Nat)
  (h1 : n > 0) (h2 : l > n) (h3 : flags.length = n) :
  solve_cars_meeting n l flags ≤ l/2 :=
  sorry

theorem flags_strictly_increasing (n l : Nat) (flags : List Nat)
  (h1 : n > 0) (h2 : l > n) (h3 : flags.length = n) :
  ∀ i : Fin (n-1), flags[i.val] < flags[i.val+1] :=
  sorry

theorem flags_within_bounds (n l : Nat) (flags : List Nat)
  (h1 : n > 0) (h2 : l > n) (h3 : flags.length = n) :
  ∀ x ∈ flags, 0 < x ∧ x < l :=
  sorry

theorem numerical_stability (n l : Nat) (flags flags_perturbed : List Nat)
  (h1 : n > 0) (h2 : l > n) (h3 : flags.length = n) 
  (h4 : flags_perturbed.length = n)
  (h5 : ∀ (i : Fin n), flags[i.val] - flags_perturbed[i.val] ≤ 1) :
  solve_cars_meeting n l flags - solve_cars_meeting n l flags_perturbed ≤ 1 :=
  sorry
-- </vc-theorems>