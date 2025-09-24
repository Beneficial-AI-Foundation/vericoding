-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_groups_size_x (deck : List Int) : Bool := sorry

@[simp]
-- </vc-definitions>

-- <vc-theorems>
theorem unique_elements_no_groups (deck : List Int) 
  (h : ∀ x ∈ deck, (List.count x deck) = 1) : 
  ¬has_groups_size_x deck := sorry

theorem repeating_elements_divisible 
  (group_size : Nat) (num_groups : Nat)
  (h1 : group_size ≥ 2) (h2 : num_groups ≥ 1)
  (deck : List Int)
  (h3 : deck = List.join (List.map (fun i => List.replicate group_size (Int.ofNat i)) (List.range num_groups))) :
  has_groups_size_x deck := sorry

theorem mixed_groups_common_factor
  (size1 size2 : Nat)
  (h1 : size1 ≥ 2) (h2 : size2 ≥ 2)
  (deck : List Int)
  (h3 : ∃ k ≥ 2, size1 % k = 0 ∧ size2 % k = 0)
  (h4 : deck = List.replicate size1 1 ++ List.replicate size2 2) :
  has_groups_size_x deck := sorry

theorem permutation_invariant
  (deck1 deck2 : List Int)
  (h : List.Perm deck1 deck2) :
  has_groups_size_x deck1 = has_groups_size_x deck2 := sorry

theorem doubled_deck_property
  (deck : List Int)
  (h : deck.length ≥ 1) :
  has_groups_size_x deck ≤ has_groups_size_x (deck ++ deck) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval has_groups_size_x [1, 2, 3, 4, 4, 3, 2, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval has_groups_size_x [1, 1, 1, 2, 2, 2, 3, 3]

/-
info: True
-/
-- #guard_msgs in
-- #eval has_groups_size_x [1, 1, 2, 2, 2, 2]
-- </vc-theorems>