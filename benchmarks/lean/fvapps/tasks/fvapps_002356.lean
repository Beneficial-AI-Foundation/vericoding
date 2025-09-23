-- <vc-preamble>
def list_sum (nums : List Nat) : Nat :=
  List.foldl Nat.add 0 nums
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rob (nums : List Nat) : Nat :=
  sorry

def elementsAtEvenIndices (nums : List Nat) : List Nat :=
  sorry

def elementsAtOddIndices (nums : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rob_nonnegative (nums : List Nat) :
  rob nums ≥ 0 :=
sorry

theorem rob_even_indices_bound (nums : List Nat) (h : nums ≠ []) :
  rob nums ≥ List.foldl Nat.max 0 (elementsAtEvenIndices nums) :=
sorry

theorem rob_odd_indices_bound (nums : List Nat) (h : nums ≠ []) :
  rob nums ≥ List.foldl Nat.max 0 (elementsAtOddIndices nums) :=
sorry

theorem rob_minimum_of_first_two (nums : List Nat) (h : nums.length ≥ 2) :
  rob nums ≥ Nat.max (nums.get ⟨0, sorry⟩) (nums.get ⟨1, sorry⟩) :=
sorry

theorem rob_subset_sum (nums : List Nat) :
  rob nums ≤ list_sum nums :=
sorry

theorem rob_empty :
  rob [] = 0 :=
sorry

theorem rob_singleton (n : Nat) :
  rob [n] = n :=
sorry

theorem rob_pair (n m : Nat) :
  rob [n, m] = Nat.max n m :=
sorry
-- </vc-theorems>