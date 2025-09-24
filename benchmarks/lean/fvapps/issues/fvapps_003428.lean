-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def presentation_agenda (friend_list : List Person) : List Person :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem presentation_agenda_structure (friend_list : List Person) :
  let result := presentation_agenda friend_list
  -- Result destinations should be subset of input destinations 
  ∀ p, p ∈ result → ∀ d, d ∈ p.dest → ∃ p', p' ∈ friend_list ∧ d ∈ p'.dest :=
  sorry

theorem presentation_agenda_unique_dests (friend_list : List Person) :
  let result := presentation_agenda friend_list
  -- Each destination appears exactly once in result
  ∀ d : String, (∃ p, p ∈ result ∧ d ∈ p.dest) → 
    ∀ p₁ p₂, p₁ ∈ result → p₂ ∈ result → d ∈ p₁.dest → d ∈ p₂.dest → p₁ = p₂ :=
  sorry

theorem presentation_agenda_valid_people (friend_list : List Person) :
  let result := presentation_agenda friend_list
  -- All people in result come from input
  ∀ p, p ∈ result → ∃ p', p' ∈ friend_list ∧ p.person = p'.person :=
  sorry

theorem presentation_agenda_nonempty_dests (friend_list : List Person) :
  let result := presentation_agenda friend_list
  -- Everyone has at least one destination
  ∀ p, p ∈ result → p.dest.length > 0 :=
  sorry

theorem presentation_agenda_unique_input_dests (friend_list : List Person) :
  let result := presentation_agenda friend_list
  -- Destinations in result appeared exactly once in input
  ∀ p, p ∈ result → ∀ d, d ∈ p.dest →
    (friend_list.filter (fun p' => d ∈ p'.dest)).length = 1 :=
  sorry

theorem presentation_agenda_shared_empty (friend_list : List Person) (d : String) :
  friend_list.length ≥ 2 →
  (∀ p, p ∈ friend_list → p.dest = [d]) →
  presentation_agenda friend_list = [] :=
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval presentation_agenda [{"person": "Abe", "dest": ["London", "Dubai"]}, {"person": "Bond", "dest": ["Melbourne", "Dubai"]}]

/-
info: []
-/
-- #guard_msgs in
-- #eval presentation_agenda [{"person": "Abe", "dest": ["Dubai"]}, {"person": "Brad", "dest": ["Dubai"]}]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval presentation_agenda [{"person": "Abe", "dest": ["London", "Dubai"]}, {"person": "Bond", "dest": ["Melbourne", "Dubai"]}, {"person": "Carrie", "dest": ["Melbourne"]}, {"person": "Damu", "dest": ["Melbourne", "Dubai", "Paris"]}]
-- </vc-theorems>