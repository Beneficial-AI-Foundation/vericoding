/-
You're putting together contact information for all the users of your website to ship them a small gift. You queried your database and got back a list of users, where each user is another list with up to two items: a string representing the user's name and their shipping zip code. Example data might look like:

```python
[["Grae Drake", 98110], ["Bethany Kok"], ["Alex Nussbacher", 94101], ["Darrell Silver", 11201]]
```
Notice that one of the users above has a name but _doesn't_ have a zip code.

Write a function `user_contacts()` that takes a two-dimensional list like the one above and returns a dictionary with an item for each user where the key is the user's name and the value is the user's zip code. If your data doesn't include a zip code then the value should be `None`.

For example, using the input above, `user_contacts()` would return this dictionary:
```python
{
    "Grae Drake": 98110,
    "Bethany Kok": None,
    "Alex Nussbacher": 94101,
    "Darrell Silver": 11201,    
}
```

You don't have to worry about leading zeros in zip codes.
-/

-- <vc-helpers>
-- </vc-helpers>

def user_contacts (contacts : List (List String)) : 
  HashMap String (Option Int) := sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded