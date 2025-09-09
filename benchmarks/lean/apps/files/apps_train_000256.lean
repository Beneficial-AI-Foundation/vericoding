def find_kth_largest (nums : List Int) (k : Nat) : Int :=
  sorry

def max_list (l : List Int) : Int :=
  sorry 

def min_list (l : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sort_desc (l : List Int) : List Int :=
  sorry

theorem find_kth_largest_element_membership
  (nums : List Int) (k : Nat) (h : k > 0) (h' : k ≤ nums.length) :
  (find_kth_largest nums k) ∈ nums :=
  sorry

theorem find_kth_largest_lower_bound
  (nums : List Int) (k : Nat) (h : k > 0) (h' : k ≤ nums.length) :
  (nums.filter (fun x => x ≥ find_kth_largest nums k)).length ≥ k :=
  sorry

theorem find_kth_largest_upper_bound
  (nums : List Int) (k : Nat) (h : k > 0) (h' : k ≤ nums.length) :
  (nums.filter (fun x => x > find_kth_largest nums k)).length < k :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_kth_largest [3, 2, 1, 5, 6, 4] 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_kth_largest [3, 2, 3, 1, 2, 4, 5, 5, 6] 4

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_kth_largest [2, 1, 3, 4, 5, 6] 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible