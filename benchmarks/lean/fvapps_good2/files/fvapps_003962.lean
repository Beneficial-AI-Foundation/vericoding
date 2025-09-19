-- <vc-preamble>
def sum : List Nat → Nat
| [] => 0
| (x::xs) => x + sum xs

def maxList : List Nat → Nat
| [] => 0
| [x] => x
| (x::xs) => max x (maxList xs)

def zipWith (f : Nat → Nat → Nat) : List Nat → List Nat → List Nat
| [], _ => []
| _, [] => []
| (x::xs), (y::ys) => f x y :: zipWith f xs ys

def pairwiseProduct (nums : List Nat) : Nat :=
  let n := nums.length
  let firstHalf := nums.take (n/2)
  let secondHalf := (nums.drop (n/2)).reverse
  sum (zipWith (fun x y => x * y) firstHalf secondHalf)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_sum (nums : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_sum_non_negative (nums : List Nat)
  (h : nums.length ≥ 2)
  (h2 : nums.length % 2 = 0) :
  min_sum nums ≥ 0 :=
sorry

theorem min_sum_upper_bound (nums : List Nat)
  (h : nums.length ≥ 2)
  (h2 : nums.length % 2 = 0) :
  min_sum nums ≤ sum nums * maxList nums :=
sorry

theorem min_sum_reverse_invariant (nums : List Nat)
  (h : nums.length ≥ 2)
  (h2 : nums.length % 2 = 0) :
  min_sum nums = min_sum nums.reverse :=
sorry

theorem min_sum_permutation_invariant (nums₁ nums₂ : List Nat)
  (h1 : nums₁.length ≥ 2)
  (h2 : nums₁.length % 2 = 0)
  (h3 : nums₁.length = nums₂.length)
  (h4 : ∀ x, nums₁.count x = nums₂.count x) :
  min_sum nums₁ = min_sum nums₂ :=
sorry

theorem min_sum_minimality (nums : List Nat)
  (h : nums.length ≥ 2)
  (h2 : nums.length % 2 = 0) :
  min_sum nums ≤ pairwiseProduct nums :=
sorry
-- </vc-theorems>