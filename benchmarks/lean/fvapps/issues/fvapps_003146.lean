-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def score_pole_vault (vaulters : List Vaulter) : List (String × String) :=
  sorry

-- Properties about valid placements
-- </vc-definitions>

-- <vc-theorems>
theorem score_pole_vault_valid_places (vaulters : List Vaulter) :
  let result := score_pole_vault vaulters
  ∀ p ∈ result, p.1 ∈ ["1st", "2nd", "3rd"] :=
sorry

theorem score_pole_vault_max_places (vaulters : List Vaulter) :
  let result := score_pole_vault vaulters
  result.length ≤ 3 :=
sorry

-- Properties about tie/jump-off formatting

theorem score_pole_vault_tie_format (vaulters : List Vaulter) :
  let result := score_pole_vault vaulters
  ∀ p ∈ result,
    p.2.contains '(' → (p.2.splitOn ",").length > 1 :=
sorry

theorem score_pole_vault_jumpoff_format (vaulters : List Vaulter) :
  let result := score_pole_vault vaulters
  ∀ p ∈ result,
    p.2.contains 'j' →
      (p.2.splitOn ",").length > 1 ∧ p.1 = "1st" :=
sorry

-- Property about names in result appearing in original vaulters 

theorem score_pole_vault_valid_names (vaulters : List Vaulter) :
  let result := score_pole_vault vaulters
  let processName (s : String) := s.trim
  ∀ p ∈ result, ∀ name ∈ p.2.splitOn ",",
    ∃ v ∈ vaulters, v.name = processName name :=
sorry

-- Property about ordering of places

theorem score_pole_vault_ordered_places (vaulters : List Vaulter) :
  let result := score_pole_vault vaulters
  result.length > 1 →
    ∀ i j, i < j → j < result.length →
      (result[i]!.1.front.toNat) ≤ (result[j]!.1.front.toNat) :=
sorry

/-
info: {'1st': 'Linda', '2nd': 'Debbie', '3rd': 'Michelle'}
-/
-- #guard_msgs in
-- #eval score_pole_vault [{"name": "Linda", "results": ["XXO", "O", "XXO", "O"]}, {"name": "Vickie", "results": ["O", "X", "", ""]}, {"name": "Debbie", "results": ["XXO", "O", "XO", "XXX"]}, {"name": "Michelle", "results": ["XO", "XO", "XXX", ""]}, {"name": "Carol", "results": ["XXX", "", "", ""]}]

/-
info: {'1st': 'Onyx', '2nd': 'Lana', '3rd': 'Alexandria, Molly, Rebecca (tie)'}
-/
-- #guard_msgs in
-- #eval score_pole_vault [{"name": "Lana", "results": ["XO", "O", "O", "XXO", "XXX"]}, {"name": "Onyx", "results": ["XXO", "XXO", "XO", "O", "XXX"]}, {"name": "Molly", "results": ["XO", "XO", "O", "XXX", ""]}, {"name": "Alexandria", "results": ["XO", "XO", "O", "XXX", ""]}, {"name": "Rebecca", "results": ["XXO", "O", "O", "XXX", ""]}]

/-
info: {'1st': 'Brett, Laura (jump-off)', '3rd': 'Sarah, Sharon (tie)'}
-/
-- #guard_msgs in
-- #eval score_pole_vault [{"name": "Sarah", "results": ["O", "X", "", ""]}, {"name": "Brett", "results": ["XO", "O", "XO", "XXO"]}, {"name": "Sharon", "results": ["O", "X", "", ""]}, {"name": "Laura", "results": ["O", "XO", "XO", "XXO"]}]
-- </vc-theorems>