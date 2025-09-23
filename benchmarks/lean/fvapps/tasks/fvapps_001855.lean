-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def path_in_zigzag_tree (label: Nat) : List Nat := sorry

theorem path_starts_with_one {label: Nat} :
  label > 0 → (path_in_zigzag_tree label).head? = some 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem path_strictly_increasing {label: Nat} (i: Nat) :
  label > 0 → i > 0 → i < (path_in_zigzag_tree label).length →
  (path_in_zigzag_tree label)[i-1]! < (path_in_zigzag_tree label)[i]! := sorry

theorem path_length_matches_binary {label: Nat} :
  label > 0 → (path_in_zigzag_tree label).length = Nat.log2 label + 1 := sorry

theorem path_elements_in_valid_range {label: Nat} (i: Nat) :
  label > 0 → i < (path_in_zigzag_tree label).length →
  2^i ≤ (path_in_zigzag_tree label)[i]! ∧ 
  (path_in_zigzag_tree label)[i]! < 2^(i+1) := sorry

theorem path_for_small_labels_one :
  path_in_zigzag_tree 1 = [1] := sorry

theorem path_for_small_labels_two_three (label: Nat) :
  label > 1 → label ≤ 3 →
  path_in_zigzag_tree label = [1, label] := sorry

theorem path_for_powers_of_two (n: Nat) :
  n > 0 →
  let label := 2^n
  (path_in_zigzag_tree label).length = n + 1 ∧
  (path_in_zigzag_tree label).head? = some 1 ∧
  (path_in_zigzag_tree label).getLast? = some label := sorry
-- </vc-theorems>