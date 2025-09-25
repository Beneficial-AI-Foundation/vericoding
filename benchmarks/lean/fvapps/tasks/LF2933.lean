-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unflatten (arr : List Nat) : List (Sum (List Nat) Nat) := sorry

def flatten {α} (l : List (Sum (List α) α)) : List α := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unflatten_type (arr : List Nat) :
  unflatten arr ≠ [] → unflatten arr ≠ [] := sorry

theorem unflatten_preserves_flatten (arr : List Nat) (h : arr ≠ []) :
  flatten (unflatten arr) = arr := sorry

theorem unflatten_sublist_len (arr : List Nat) (sublist : List Nat) :
  (Sum.inl sublist) ∈ unflatten arr → 
  sublist ≠ [] → sublist[0]! ≥ sublist.length := sorry

theorem unflatten_small_nums (arr : List Nat) (item : Nat) :
  (Sum.inr item) ∈ unflatten arr →
  item ≤ 2 := sorry

theorem unflatten_all_small (arr : List Nat) :
  (∀ x ∈ arr, x ≤ 2) → unflatten arr = arr.map Sum.inr := sorry

theorem unflatten_single_large (n : Nat) :
  n ≥ 3 → unflatten [n] = [Sum.inl [n]] := sorry
-- </vc-theorems>