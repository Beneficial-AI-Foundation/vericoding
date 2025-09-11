-- <vc-preamble>
def namelist (names : List (String × String)) : String :=
  sorry

def containsSubstr (s₁ s₂ : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem namelist_empty_list :
  namelist [] = "" :=
sorry

theorem namelist_single_name (name : String) :
  namelist [(name, "name")] = name :=
sorry

theorem namelist_multiple_names {n : ℕ} (names : List (String × String))
  (h1 : names.length > 1)
  (h2 : ∀ p ∈ names, p.2 = "name") :
  let result := namelist names;
  let all_names := names.map Prod.fst;
  -- Result contains all original names
  (∀ name ∈ all_names, containsSubstr result name)
  -- Has & separator
  ∧ containsSubstr result " & "
  -- Has correct number of commas
  ∧ (String.count result ',' = names.length - 2)
  -- Last name appears after &
  ∧ (result.splitOn " & ").get! 1 = names.getLast?.get!.1 :=
sorry

/-
info: 'Bart, Lisa & Maggie'
-/
-- #guard_msgs in
-- #eval namelist [{"name": "Bart"}, {"name": "Lisa"}, {"name": "Maggie"}]

/-
info: 'Bart & Lisa'
-/
-- #guard_msgs in
-- #eval namelist [{"name": "Bart"}, {"name": "Lisa"}]

/-
info: ''
-/
-- #guard_msgs in
-- #eval namelist []
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded