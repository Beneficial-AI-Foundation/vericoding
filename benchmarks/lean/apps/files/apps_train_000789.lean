-- <vc-preamble>
def find_largest_triangle (n : Nat) (nums : List Nat) : String × List Nat := sorry

def is_valid_triangle (sides : List Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum (l : List Nat) : Nat := 
  l.foldl (·+·) 0
-- </vc-definitions>

-- <vc-theorems>
theorem find_largest_triangle_empty_input 
  (nums : List Nat) (h : nums.length < 3) : 
  find_largest_triangle nums.length nums = ("NO", []) := sorry

theorem find_largest_triangle_returns_valid
  (nums : List Nat) (h : nums.length ≥ 3)
  (h2 : (find_largest_triangle nums.length nums).1 = "YES") :
  let result := (find_largest_triangle nums.length nums).2
  is_valid_triangle result ∧ 
  result.length = 3 ∧
  ∀ x ∈ result, x ∈ nums := sorry

theorem find_largest_triangle_is_max
  (nums : List Nat) (h : nums.length ≥ 3)
  (h2 : (find_largest_triangle nums.length nums).1 = "YES") :
  let result := (find_largest_triangle nums.length nums).2
  ∀ i j k, i < nums.length → j < nums.length → k < nums.length →
  i ≠ j → j ≠ k → i ≠ k →
  is_valid_triangle [nums.get! i, nums.get! j, nums.get! k] →
  list_sum [nums.get! i, nums.get! j, nums.get! k] ≤ list_sum result := sorry

theorem find_largest_triangle_no_implies_no_valid
  (nums : List Nat) (h : nums.length ≥ 3)
  (h2 : (find_largest_triangle nums.length nums).1 = "NO") :
  ∀ i j k, i < nums.length → j < nums.length → k < nums.length →
  i ≠ j → j ≠ k → i ≠ k →
  ¬is_valid_triangle [nums.get! i, nums.get! j, nums.get! k] := sorry

theorem find_largest_triangle_preserves_valid_triangle
  (sides : List Nat) (h : sides.length = 3) 
  (h2 : is_valid_triangle sides) :
  find_largest_triangle sides.length sides = ("YES", sides) := sorry
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded