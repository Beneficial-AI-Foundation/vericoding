-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pagination_text (pageNumber pageSize totalProducts : Nat) : String := sorry

theorem pagination_format
    {pageNumber pageSize totalProducts : Nat}
    (h1 : pageNumber ≥ 1)
    (h2 : pageNumber ≤ 1000)
    (h3 : pageSize ≥ 1)
    (h4 : pageSize ≤ 1000)
    (h5 : totalProducts ≥ 1)
    (h6 : totalProducts ≤ 10000) :
    let result := pagination_text pageNumber pageSize totalProducts;
    -- result starts with "Showing "
    ∃ rest : String, result = "Showing " ++ rest
    ∧
    -- result ends with " Products."
    ∃ start : String, result = start ++ " Products."
    ∧
    -- result contains " to "
    ∃ before after : String, result = before ++ " to " ++ after
    ∧
    -- result contains " of "
    ∃ before after : String, result = before ++ " of " ++ after := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pagination_numbers
    {pageNumber pageSize totalProducts : Nat}
    (h1 : pageNumber ≥ 1)
    (h2 : pageNumber ≤ 1000)
    (h3 : pageSize ≥ 1)
    (h4 : pageSize ≤ 1000)
    (h5 : totalProducts ≥ 1)
    (h6 : totalProducts ≤ 10000)
    (h7 : (pageNumber - 1) * pageSize < totalProducts) :
    ∃ first last total : Nat,
    first ≤ last
    ∧ last ≤ total
    ∧ total = totalProducts
    ∧ first = pageSize * (pageNumber - 1) + 1
    ∧ last ≤ first + pageSize - 1 := sorry

theorem pagination_bounds
    {pageNumber pageSize totalProducts : Nat}
    (h1 : pageNumber ≥ 1)
    (h2 : pageNumber ≤ 1000)
    (h3 : pageSize ≥ 1)
    (h4 : pageSize ≤ 1000)
    (h5 : totalProducts ≥ 1)
    (h6 : totalProducts ≤ 10000) :
    ∃ first last : Nat,
    last ≤ totalProducts := sorry

/-
info: 'Showing 1 to 10 of 30 Products.'
-/
-- #guard_msgs in
-- #eval pagination_text 1 10 30

/-
info: 'Showing 21 to 26 of 26 Products.'
-/
-- #guard_msgs in
-- #eval pagination_text 3 10 26

/-
info: 'Showing 1 to 8 of 8 Products.'
-/
-- #guard_msgs in
-- #eval pagination_text 1 10 8
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded