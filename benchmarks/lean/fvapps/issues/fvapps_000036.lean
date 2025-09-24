-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_pile_numbers (n : Nat) (pile_sizes : List Nat) (m : Nat) (labels : List Nat) : List Nat :=
  sorry

-- Properties about length and valid pile numbers
-- </vc-definitions>

-- <vc-theorems>
theorem find_pile_nums_length (n : Nat) (pile_sizes : List Nat) (m : Nat) (labels : List Nat)
    (h1 : pile_sizes.length = n)
    (h2 : labels.length = m)
    (h3 : n > 0)
    (h4 : m > 0)
    (h5 : ∀ x ∈ pile_sizes, x > 0)
    (h6 : ∀ x ∈ labels, x > 0) :
    (find_pile_numbers n pile_sizes m labels).length = labels.length :=
  sorry

theorem find_pile_nums_valid_output (n : Nat) (pile_sizes : List Nat) (m : Nat) (labels : List Nat)
    (h1 : pile_sizes.length = n)
    (h2 : labels.length = m)
    (h3 : n > 0)
    (h4 : m > 0)
    (h5 : ∀ x ∈ pile_sizes, x > 0)
    (h6 : ∀ x ∈ labels, x > 0) :
    ∀ x ∈ find_pile_numbers n pile_sizes m labels, 1 ≤ x ∧ x ≤ n :=
  sorry

-- Property about correct pile indices based on prefix sums

theorem find_pile_nums_correct_indices (n : Nat) (pile_sizes : List Nat) (m : Nat) (labels : List Nat)
    (h1 : pile_sizes.length = n)
    (h2 : labels.length = m)
    (h3 : n > 0)
    (h4 : m > 0)
    (h5 : ∀ x ∈ pile_sizes, x > 0)
    (h6 : ∀ x ∈ labels, x > 0) :
    ∀ (i : Nat) (label : Nat) (pile_num : Nat),
      (label ∈ labels) →
      (pile_num ∈ find_pile_numbers n pile_sizes m labels) →
      label ≤ (List.take i pile_sizes).sum →
      pile_num ≤ i :=
  sorry

-- Property about identical labels mapping to same pile

theorem find_pile_nums_identical_labels (n : Nat) (pile_sizes : List Nat) (label : Nat)
    (h1 : pile_sizes.length = n)
    (h2 : n > 0)
    (h3 : ∀ x ∈ pile_sizes, x > 0)
    (h4 : label > 0) :
    let labels := List.replicate 3 label
    let result := find_pile_numbers n pile_sizes 3 labels
    ∀ (x y : Nat), x ∈ result → y ∈ result → x = y :=
  sorry

-- Property about single pile case

theorem find_pile_nums_single_pile (pile_size : Nat)
    (h : pile_size > 0) :
    find_pile_numbers 1 [pile_size] 1 [1] = [1] :=
  sorry

/-
info: [1, 5, 3]
-/
-- #guard_msgs in
-- #eval find_pile_numbers 5 [2, 7, 3, 4, 9] 3 [1, 25, 11]

/-
info: [2, 3]
-/
-- #guard_msgs in
-- #eval find_pile_numbers 3 [1, 2, 3] 2 [2, 6]
-- </vc-theorems>