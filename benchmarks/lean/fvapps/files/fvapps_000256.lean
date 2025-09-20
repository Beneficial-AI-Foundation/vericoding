-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_kth_largest (nums : List Int) (k : Nat) : Int :=
  sorry

def max_list (l : List Int) : Int :=
  sorry

def min_list (l : List Int) : Int :=
  sorry

def sort_desc (l : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>