-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_teams (n: Nat) (x: Nat) (skills: List Nat) : Nat :=
  sorry

def list_sort (l: List Nat) : List Nat :=
  sorry

def list_sum (l: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_teams_bounds
  (n: Nat) (x: Nat) (skills: List Nat)
  (h1: skills.length = n)
  (h2: ∀ s ∈ skills, s ≥ 1 ∧ s ≤ 100) :
  let result := max_teams n x skills
  0 ≤ result ∧ result ≤ n :=
sorry

theorem max_teams_sort_invariant
  (n: Nat) (x: Nat) (skills: List Nat)
  (h: skills.length = n) :
  max_teams n x skills = max_teams n x (list_sort skills) :=
sorry

theorem max_teams_impossible_target
  (n: Nat) (x: Nat) (skills: List Nat)
  (h1: skills.length = n)
  (h2: x > (list_sum skills) * n) :
  max_teams n x skills = 0 :=
sorry

theorem max_teams_min_requirement
  (n: Nat) (skills: List Nat)
  (h1: skills.length = n)
  (h2: ∀ s ∈ skills, s ≥ 1) :
  max_teams n 1 skills = (List.filter (λ s => s ≥ 1) skills).length :=
sorry

theorem max_teams_empty
  (x: Nat) :
  max_teams 0 x [] = 0 :=
sorry

theorem max_teams_uniform_skills
  (n: Nat) (skill: Nat)
  (h1: skill ≥ 1)
  (h2: skill ≤ 100) :
  max_teams n skill (List.replicate n skill) = n :=
sorry
-- </vc-theorems>