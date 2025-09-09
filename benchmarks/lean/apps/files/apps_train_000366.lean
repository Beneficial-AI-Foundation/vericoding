def maximum_gap (nums : List Nat) : Nat :=
  sorry

def Permutation (l1 l2 : List α) : Prop :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sort (l : List α) (lt : α → α → Bool) : List α :=
  sorry

theorem maximum_gap_empty_or_singleton {nums : List Nat} : 
  nums.length ≤ 1 → maximum_gap nums = 0 :=
  sorry

theorem maximum_gap_nonnegative {nums : List Nat} :
  maximum_gap nums ≥ 0 :=
  sorry

theorem maximum_gap_bounded {nums : List Nat} :
  nums.length > 0 →
  maximum_gap nums ≤ List.foldl Nat.max 0 nums - List.foldl Nat.min 0 nums :=
  sorry

theorem maximum_gap_is_max_consecutive_diff {nums : List Nat} (h : nums.length > 1) :
  let sorted := sort nums (fun x y => x < y)
  let gaps := List.zipWith (fun x y => y - x) sorted (List.drop 1 sorted)
  maximum_gap nums = List.foldl Nat.max 0 gaps :=
  sorry

theorem maximum_gap_permutation_invariant {nums₁ nums₂ : List Nat} :
  nums₁.length > 1 →
  Permutation nums₁ nums₂ →
  maximum_gap nums₁ = maximum_gap nums₂ :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval maximum_gap [3, 6, 9, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval maximum_gap [10]

/-
info: 3
-/
-- #guard_msgs in
-- #eval maximum_gap [1, 2, 2, 5, 7, 10]

-- Apps difficulty: interview
-- Assurance level: unguarded