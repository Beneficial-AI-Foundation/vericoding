-- <vc-helpers>
-- </vc-helpers>

def generate_binary_pattern (k : Nat) : List (List String) := sorry

theorem pattern_length (k : Nat) (h : 0 < k) (h2 : k ≤ 10) :
  let result := generate_binary_pattern k
  (result.length = k) ∧ 
  (∀ row ∈ result, (row.length = k)) := sorry

theorem all_binary_strings (k : Nat) (h : 0 < k) (h2 : k ≤ 10) :
  let result := generate_binary_pattern k
  ∀ row ∈ result,
    ∀ num ∈ row,
      (∀ c ∈ num.data, c = '0' ∨ c = '1') ∧
      (num.data ≠ [] → List.head! num.data = '1') := sorry

theorem increasing_values (k : Nat) (h : 0 < k) (h2 : k ≤ 10) :
  let result := generate_binary_pattern k
  ∀ row ∈ result,
    let binary_nums := row.map (fun s => String.toNat! s)
    ∀ i, i + 1 < binary_nums.length →
      binary_nums[i]! < binary_nums[i+1]! := sorry

/-
info: ['1']
-/
-- #guard_msgs in
-- #eval generate_binary_pattern 1

/-
info: ['1 10', '11 100']
-/
-- #guard_msgs in
-- #eval generate_binary_pattern 2

/-
info: ['1 10 11', '100 101 110', '111 1000 1001']
-/
-- #guard_msgs in
-- #eval generate_binary_pattern 3

-- Apps difficulty: interview
-- Assurance level: unguarded