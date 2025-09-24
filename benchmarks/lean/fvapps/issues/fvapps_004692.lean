-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def user_contacts (contacts : List (List String)) : 
  HashMap String (Option Int) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_missing_zips (names : List String) :
    let contacts := names.map (fun name => [name])
    let result := user_contacts contacts
    contacts.length = result.size ∧ 
    ∀ k, result.get k = none ∨ result.get k = some none := sorry

theorem all_have_zips (contacts : List (String × Int))
    (h₁ : ∀ (p₁ p₂ : String × Int), p₁ ∈ contacts → p₂ ∈ contacts → p₁ ≠ p₂ → p₁.1 ≠ p₂.1)
    (h₂ : ∀ pair ∈ contacts, 10000 ≤ pair.2 ∧ pair.2 ≤ 99999) :
    let result := user_contacts (contacts.map (fun p => [p.1, toString p.2]))
    contacts.length = result.size ∧
    (∀ k, (result.get k).isSome → (Option.get! (result.get k)).isSome) ∧
    (∀ pair ∈ contacts, result.get pair.1 = some (some pair.2)) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval user_contacts [["Grae Drake", 98110], ["Bethany Kok"], ["Alex Nussbacher", 94101]]

/-
info: {}
-/
-- #guard_msgs in
-- #eval user_contacts []

/-
info: expected3
-/
-- #guard_msgs in
-- #eval user_contacts [["User1", 12345], ["User2", 67890]]
-- </vc-theorems>