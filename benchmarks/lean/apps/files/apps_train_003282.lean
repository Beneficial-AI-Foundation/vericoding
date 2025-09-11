-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiplication_table (rows cols : Nat) : List (List Nat) := sorry

theorem multiplication_table_dimensions 
  (rows cols : Nat) (h1 : rows > 0) (h2 : cols > 0) :
  let table := multiplication_table rows cols
  (table.length = rows) ∧ 
  (∀ row ∈ table, row.length = cols) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiplication_table_values
  (rows cols : Nat) (h1 : rows > 0) (h2 : cols > 0) :
  let table := multiplication_table rows cols
  ∀ i j, i < rows → j < cols →
    table[i]!.get! j = (i + 1) * (j + 1) := sorry

theorem multiplication_table_square_properties
  (size : Nat) (h : size > 0) :
  let table := multiplication_table size size
  (∀ i, i < size → table[i]!.get! i = (i + 1) * (i + 1)) ∧
  (∀ i j, i < size → j < size → 
    table[i]!.get! j = table[j]!.get! i) := sorry

/-
info: [[1, 2], [2, 4]]
-/
-- #guard_msgs in
-- #eval multiplication_table 2 2

/-
info: [[1, 2, 3], [2, 4, 6], [3, 6, 9]]
-/
-- #guard_msgs in
-- #eval multiplication_table 3 3

/-
info: [[1, 2, 3, 4, 5], [2, 4, 6, 8, 10]]
-/
-- #guard_msgs in
-- #eval multiplication_table 2 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible