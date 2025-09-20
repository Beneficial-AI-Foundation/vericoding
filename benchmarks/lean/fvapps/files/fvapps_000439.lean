-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMin (arr : List Int) : Int :=
  sorry

def rotateList (xs : List Int) (n : Nat) : List Int :=
  sorry

def listMin (xs : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findMin_singleton (n : Int) :
  findMin [n] = n :=
sorry

theorem findMin_pair (a b : Int) :
  findMin [a, b] = min a b :=
sorry

theorem findMin_triple (a b c : Int) :
  findMin [a, b, c] = min (min a b) c :=
sorry

theorem findMin_rotated_sorted_unique {nums : List Int} (h1 : nums.length ≥ 4)
    (h2 : List.Pairwise (· ≠ ·) nums) (h3 : ∀ x ∈ nums, -100 ≤ x ∧ x ≤ 100) :
  findMin (rotateList nums (nums.length / 2)) = listMin nums :=
sorry
-- </vc-theorems>