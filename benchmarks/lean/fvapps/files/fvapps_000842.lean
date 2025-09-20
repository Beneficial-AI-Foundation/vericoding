-- <vc-preamble>
def pow (x: Int) (n: Nat) : Int :=
  match n with
  | 0 => 1
  | n + 1 => x * pow x n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_special_sum (n: Int) (k: Int) : Int :=
  sorry

def solve_case (n: Int) (k: Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_special_sum_nonnegative
  (n: Int) (k: Int)
  (hn: n ≥ 0) (hk: k ≥ 2) (hk2: k ≤ 100) :
  calculate_special_sum n k ≥ 0 :=
sorry

theorem calculate_special_sum_upper_bound
  (n: Int) (k: Int) (power: Nat)
  (hn: n ≥ 0) (hk: k ≥ 2) (hk2: k ≤ 100)
  (hp: pow k power ≤ n) :
  calculate_special_sum n k ≤ (n * (n+1))/2 :=
sorry

theorem calculate_special_sum_negative_input
  (n: Int) (k: Int)
  (hn: n < 0) (hk: k ≥ 2) (hk2: k ≤ 100) :
  calculate_special_sum n k = 0 :=
sorry

theorem solve_case_format
  (n: Int) (k: Int)
  (hn: n ≥ 0) (hk: k ≥ 2) (hk2: k ≤ 100) :
  solve_case n k = "Case #1: " ++ toString (calculate_special_sum n k) :=
sorry
-- </vc-theorems>