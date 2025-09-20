-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_consecutive_power (arr : List Int) (k : Nat) : Int :=
sorry

def sum_sublist (l : List Int) (i : Nat) (len : Nat) : Int :=
sorry

def list_sum (l : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_consecutive_power_is_k_consecutive
  {arr : List Int} {k : Nat} (h : k ≤ arr.length) :
  ∃ i, i + k ≤ arr.length ∧
    find_max_consecutive_power arr k = sum_sublist arr i k :=
sorry

theorem find_max_consecutive_power_is_maximum
  {arr : List Int} {k : Nat} (h : k ≤ arr.length) :
  ∀ i, i + k ≤ arr.length →
    sum_sublist arr i k ≤ find_max_consecutive_power arr k :=
sorry

theorem find_max_consecutive_power_equals_sum_when_k_equals_length
  {arr : List Int} :
  find_max_consecutive_power arr arr.length = list_sum arr :=
sorry

theorem find_max_consecutive_power_nonnegative
  {arr : List Int} {k : Nat} (h : k ≤ arr.length)
  (h_nonneg : ∀ x ∈ arr, 0 ≤ x) :
  0 ≤ find_max_consecutive_power arr k :=
sorry
-- </vc-theorems>