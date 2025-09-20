-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findSmallestCommonMultiple (numbers : List Nat) : Nat := sorry
def findGreatestCommonFactor (numbers : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lcm_divisibility {numbers : List Nat} (h : numbers ≠ []) : 
  ∀ n ∈ numbers, findSmallestCommonMultiple numbers % n = 0 := sorry

theorem lcm_lower_bound {numbers : List Nat} (h : numbers ≠ []) : 
  findSmallestCommonMultiple numbers ≥ (List.foldl Nat.max 0 numbers) := sorry

theorem gcf_divides {numbers : List Nat} (h : numbers ≠ []) :
  ∀ n ∈ numbers, n % findGreatestCommonFactor numbers = 0 := sorry 

theorem gcf_upper_bound {numbers : List Nat} (h : numbers ≠ []) :
  findGreatestCommonFactor numbers ≤ (List.foldl Nat.min (List.head! numbers) (List.tail! numbers)) := sorry

theorem lcm_identity (n : Nat) :
  findSmallestCommonMultiple [n] = n := sorry

theorem gcf_identity (n : Nat) :
  findGreatestCommonFactor [n] = n := sorry
-- </vc-theorems>