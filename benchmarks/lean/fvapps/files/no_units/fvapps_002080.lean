-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_xor_basket (nums: List Nat) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_format {nums: List Nat} (h1: nums.length > 0) 
  (h2: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000) :
  let result := solve_xor_basket nums
  (result.length = nums.length) ∧ 
  (∀ r ∈ result, 
    r = "0" ∨ 
    (let parts := r.split (· = ' ')
     let count := parts.head!.toNat!
     parts.length = count + 1 ∧
     (∀ i ∈ parts.tail, 
       let idx := i.toNat!
       0 ≤ idx ∧ idx < nums.length) ∧
     parts.tail.eraseDups = parts.tail)) :=
  sorry

theorem xor_property {nums: List Nat} (h1: nums.length > 0)
  (h2: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000) :
  let result := solve_xor_basket nums
  ∀ i, i < nums.length →
    (result[i]? = some "0") ∨
    (∃ parts : List String,
     parts = (result[i]?).get!.split (· = ' ') ∧
     ∃ indices : List Nat,
     indices = parts.tail.map (·.toNat!) ∧
     (∀ idx ∈ indices, idx < nums.length) ∧
     let xor_result := indices.foldl (fun acc idx => Nat.xor acc (nums.get! idx)) 0
     xor_result = nums[i]?) :=
  sorry
-- </vc-theorems>