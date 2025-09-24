-- <vc-preamble>
def group_in_10s (nums : List Nat) : List (Option (List Nat)) := sorry

theorem group_in_10s_empty (nums : List Nat) :
  nums = [] → group_in_10s nums = [] := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listMax (l : List Nat) : Nat :=
match l with
| [] => 0
| (x::xs) => max x (listMax xs)
-- </vc-definitions>

-- <vc-theorems>
theorem group_in_10s_sorted (nums : List Nat) (group : List Nat) :
  group ∈ (group_in_10s nums).filterMap id → 
  ∀ i j, i < j → j < group.length → 
  ∀ h1 : i < group.length, ∀ h2 : j < group.length, 
  group.get ⟨i,h1⟩ ≤ group.get ⟨j,h2⟩ := sorry

theorem group_in_10s_same_tens_digit (nums : List Nat) (group : List Nat) (group_idx : Nat) :
  some group = (group_in_10s nums).get? group_idx → 
  ∀ n ∈ group, n / 10 = group_idx := sorry

theorem group_in_10s_preserves_elements (nums : List Nat) :
  List.length (List.join ((group_in_10s nums).filterMap id)) = List.length nums ∧
  ∀ n ∈ nums, n ∈ List.join ((group_in_10s nums).filterMap id) := sorry

theorem group_in_10s_single (n : Nat) :
  n ≤ 1000 →
  let result := group_in_10s [n]
  (∀ i < n/10, result.get? i = some none) ∧ 
  result.get? (n/10) = some (some [n]) ∧
  result.length = n/10 + 1 := sorry

theorem group_in_10s_max_length (nums : List Nat) :
  nums ≠ [] →
  (∀ n ∈ nums, n ≤ 99) →
  (group_in_10s nums).length = (listMax nums) / 10 + 1 := sorry

/-
info: 11
-/
-- #guard_msgs in
-- #eval len group_in_10s(100)
-- </vc-theorems>