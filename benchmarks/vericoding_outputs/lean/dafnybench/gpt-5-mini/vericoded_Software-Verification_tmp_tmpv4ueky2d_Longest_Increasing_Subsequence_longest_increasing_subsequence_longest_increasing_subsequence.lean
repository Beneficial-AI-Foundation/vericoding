import Mathlib
-- <vc-preamble>
def find_max (x y : Int) : Int :=
if x > y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Compute the length of the longest strictly increasing subsequence for a List of Ints.
    This is an O(n^2) dynamic programming helper implemented purely with lists.
--/
def lis_len_of_list (xs : List Int) : Nat :=
  let (_, rev_dp) := xs.foldl (fun (acc : List Int × List Nat) x =>
    let (rvals, rdp) := acc
    -- bring values/dp into forward order to examine previous elements
    let vals := rvals.reverse
    let dp := rdp.reverse
    let zipped := vals.zip dp
    -- best_prev = max { dp[j] | vals[j] < x } (0 if none)
    let best_prev := zipped.foldl (fun acc' pr => if decide (pr.fst < x) then max acc' pr.snd else acc') 0
    let best := best_prev + 1
    (x :: rvals, best :: rdp)
  ) ([], [])
  let final_dp := rev_dp.reverse
  final_dp.foldl (fun a b => max a b) 0

-- End LLM HELPER
-- </vc-helpers>

-- <vc-definitions>
def longest_increasing_subsequence (nums : Array Int) : Int :=
let len := lis_len_of_list nums.toList
1 + Int.ofNat (len - 1)
-- </vc-definitions>

-- <vc-theorems>
theorem longest_increasing_subsequence_spec (nums : Array Int) :
(1 ≤ nums.size ∧ nums.size ≤ 2500) →
(∀ i, 0 ≤ i ∧ i < nums.size → -10000 ≤ nums[i]! ∧ nums[i]! ≤ 10000) →
longest_increasing_subsequence nums ≥ 1 :=
by
  intro hsize hbounds
  -- lis_len_of_list produces a Nat; Int.ofNat of any Nat is ≥ 0
  have hnonneg : 0 ≤ Int.ofNat (lis_len_of_list nums.toList - 1) := Int.ofNat_nonneg (lis_len_of_list nums.toList - 1)
  calc
    longest_increasing_subsequence nums = 1 + Int.ofNat (lis_len_of_list nums.toList - 1) := rfl
    _ ≥ 1 + 0 := by apply add_le_add_left hnonneg 1
    _ = 1 := by simp
-- </vc-theorems>
