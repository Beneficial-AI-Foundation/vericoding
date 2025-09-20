-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def base_neg2 (n : Int) : String := sorry

def binaryStringToNegBase2 (s : String) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_neg2_valid_binary (n : Int) :
  let s := base_neg2 n
  ∀ c ∈ s.data, c = '0' ∨ c = '1' := sorry

theorem base_neg2_roundtrip (n : Int) : 
  binaryStringToNegBase2 (base_neg2 n) = n := sorry

theorem base_neg2_positive (n : Int) :
  n ≥ 0 →
  (base_neg2 n).length > 0 ∧ 
  (base_neg2 n).data.head? ≠ some '-' := sorry

theorem base_neg2_zero :
  base_neg2 0 = "0" := sorry

theorem base_neg2_length (n : Int) (h : n > 0) :
  let binary_length := String.length (base_neg2 n)
  binary_length ≤ String.length (toString n) + 2 := sorry
-- </vc-theorems>