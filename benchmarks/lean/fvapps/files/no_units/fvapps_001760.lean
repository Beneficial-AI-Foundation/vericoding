-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nums_same_consec_diff (n k : Nat) : List Nat := sorry

def absDiff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_case (n : Nat) (h : 1 ≤ n ∧ n ≤ 9) :
  let result := nums_same_consec_diff 1 n
  List.length result = 10 ∧ 
  (∀ x ∈ result, 0 ≤ x ∧ x ≤ 9) ∧
  result = List.range 10 := sorry

theorem result_properties (n k : Nat) (h1 : 2 ≤ n ∧ n ≤ 9) (h2 : k ≤ 9) :
  let result := nums_same_consec_diff n k
  let str_len := fun x => String.length (toString x)
  let first_digit := fun x => (toString x).data.get! 0
  let digit_at := fun x i => ((toString x).data.get! i).toNat
  (∀ x ∈ result, str_len x = n) ∧
  (∀ x ∈ result, first_digit x ≠ '0') ∧
  (∀ x ∈ result, ∀ i < n-1, 
    absDiff (digit_at x i) (digit_at x (i+1)) = k) := sorry

theorem zero_difference (n : Nat) (h : 2 ≤ n ∧ n ≤ 9) :
  let result := nums_same_consec_diff n 0
  (∀ x ∈ result, List.length ((toString x).data.eraseDups) = 1) ∧
  List.length result = 9 := sorry

theorem max_difference (n : Nat) (h : 2 ≤ n ∧ n ≤ 9) :
  let result := nums_same_consec_diff n 9
  let digit_at := fun x i => ((toString x).data.get! i).toNat
  ∀ x ∈ result, ∀ i < n-1,
    absDiff (digit_at x i) (digit_at x (i+1)) = 9 := sorry
-- </vc-theorems>