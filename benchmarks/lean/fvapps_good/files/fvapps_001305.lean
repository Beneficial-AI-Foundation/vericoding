-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_github_shades (contributions: List Nat) : List String := sorry

def isValidResultString (s: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_github_shades_result_type {contributions: List Nat} (h: contributions.length > 0) :
  let result := count_github_shades contributions
  result.all (fun x => isValidResultString x) := sorry

theorem count_github_shades_sorted {contributions: List Nat} (h: contributions.length > 0) :
  let result := count_github_shades contributions
  let nums := result.map (fun x => (x.splitOn ": ").head!.toNat!)
  ∀ i, i + 1 < nums.length → nums[i]! ≤ nums[i+1]! := sorry

theorem count_github_shades_counts_sum {contributions: List Nat} (h: contributions.length > 0) :
  let result := count_github_shades contributions
  let counts := result.map (fun x => (x.splitOn ": ").getLast!.toNat!)
  counts.foldl (·+·) 0 = contributions.length := sorry

theorem count_github_shades_unique_values {contributions: List Nat} (h: contributions.length > 0) :
  let result := count_github_shades contributions
  let nums := result.map (fun x => (x.splitOn ": ").head!.toNat!)
  ∀ i j, i < nums.length → j < nums.length → i ≠ j → nums[i]! ≠ nums[j]! := sorry
-- </vc-theorems>