-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_k_diff_pairs (nums : List Int) (k : Int) : Int :=
  sorry

def countOccurrences (nums : List Int) (x : Int) : Nat :=
  sorry

def dedup (nums : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem k_diff_pairs_property :
  ∀ (nums : List Int) (k : Int),
  let result := find_k_diff_pairs nums k
  result ≥ 0 ∧ (k < 0 → result = 0) :=
sorry

theorem positive_k_pairs_symmetric :
  ∀ (nums : List Int) (k : Int),
  k > 0 →
  find_k_diff_pairs nums (-k) = 0 :=
sorry

theorem k_diff_pairs_subset :
  ∀ (nums : List Int) (k : Int),
  k > 0 →
  nums.length > 0 →
  let subset := nums.take (nums.length / 2)
  find_k_diff_pairs subset k ≤ find_k_diff_pairs nums k :=
sorry
-- </vc-theorems>