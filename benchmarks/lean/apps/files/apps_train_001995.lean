-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinaryString := String

def solve_binary_string_concat (strings : List BinaryString) (operations : List (Nat × Nat)) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_binary_string_concat_basic_properties 
  (strings : List BinaryString) 
  (operations : List (Nat × Nat))
  (h1 : strings.length ≥ 2)
  (h2 : strings.length ≤ 5) 
  (h3 : operations.length ≥ 1)
  (h4 : operations.length ≤ 3)
  (h5 : ∀ s ∈ strings, s.length ≥ 1)
  (h6 : ∀ s ∈ strings, s.length ≤ 20)
  (h7 : ∀ s ∈ strings, ∀ c ∈ s.data, c = '0' ∨ c = '1')
  (h8 : ∀ op ∈ operations, op.1 ≥ 1 ∧ op.1 ≤ strings.length ∧ op.2 ≥ 1 ∧ op.2 ≤ strings.length) :
  let result := solve_binary_string_concat strings operations
  (∀ x ∈ result, x ≥ 0) ∧
  (result.length = operations.length) ∧
  (∀ x ∈ result, x ≤ 20) := sorry

theorem solve_binary_string_concat_all_zeros
  (strings : List BinaryString)
  (h1 : strings.length ≥ 2)
  (h2 : strings.length ≤ 5)
  (h3 : ∀ s ∈ strings, s = "0") :
  solve_binary_string_concat strings [(1,2)] = [0] := sorry

theorem solve_binary_string_concat_all_ones
  (strings : List BinaryString)
  (h1 : strings.length ≥ 2)
  (h2 : strings.length ≤ 5)
  (h3 : ∀ s ∈ strings, s = "1") :
  solve_binary_string_concat strings [(1,2)] = [0] := sorry

/-
info: [1, 2, 0]
-/
-- #guard_msgs in
-- #eval solve_binary_string_concat ["01", "10", "101", "11111", "0"] [(1, 2), (6, 5), (4, 4)]

/-
info: [1, 1, 1, 2, 1, 2]
-/
-- #guard_msgs in
-- #eval solve_binary_string_concat ["01", "1", "0011", "0", "01"] [(5, 5), (3, 2), (4, 2), (6, 7), (5, 1), (9, 7)]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval solve_binary_string_concat ["0", "1"] [(1, 2)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded