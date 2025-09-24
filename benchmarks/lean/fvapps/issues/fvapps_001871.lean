-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_team (required_skills : List String) (people : List Person) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_team_result_valid
  (required_skills : List String)
  (people : List Person) 
  (h1 : required_skills ≠ [])
  (h2 : people ≠ []) :
  let result := find_smallest_team required_skills people
  -- Result indices are valid
  ∀ i ∈ result, i < people.length := sorry

theorem find_smallest_team_covers_skills
  (required_skills : List String)
  (people : List Person)
  (h1 : required_skills ≠ [])
  (h2 : people ≠ []) :
  let result := find_smallest_team required_skills people
  let covered_skills := (result.filterMap (λ i => if h : i < people.length then some (people[i]'h).skills else none)).join
  ∀ skill ∈ required_skills, skill ∈ covered_skills := sorry

theorem find_smallest_team_singleton
  (required_skills : List String)
  (people : List Person)
  (h : ∃ p ∈ people, ∀ s ∈ required_skills, s ∈ p.skills) :
  let result := find_smallest_team required_skills people
  result.length = 1 := sorry

theorem find_smallest_team_disjoint_skills
  (skills : List String)
  (people : List Person)
  (h1 : skills.length = people.length)
  (h2 : ∀ (i : Fin people.length), (people[i]).skills = [skills[i]]) :
  let result := find_smallest_team skills people
  result.length = skills.length := sorry

/-
info: [0, 2]
-/
-- #guard_msgs in
-- #eval sorted find_smallest_team(req_skills1, people1)

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval sorted find_smallest_team(req_skills2, people2)
-- </vc-theorems>