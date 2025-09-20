-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_divisible_numbers (start final divisor : Int) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_divisible_numbers_properties
  (start length divisor : Int)
  (h1 : start ≥ -1000) (h2 : start ≤ 1000)
  (h3 : length ≥ 0) (h4 : length ≤ 1000) 
  (h5 : divisor > 0) (h6 : divisor ≤ 100) : 
  let final := start + length;
  let result := find_divisible_numbers start final divisor;
  let count := result.1;
  let last := result.2;
  count ≥ 0 ∧
  (count > 0 → 
    last % divisor = 0 ∧ 
    start ≤ last ∧ 
    last ≤ final) ∧
  (count = 0 → last = 0) ∧
  count = ((List.range (Int.toNat (final - start + 1))).map Int.ofNat |>.filter (fun x => (x + start) % divisor = 0)).length ∧
  (count > 0 → ∀ x, last < x → x ≤ final → x % divisor ≠ 0) :=
  sorry

theorem empty_range_properties
  (start divisor : Int)
  (h1 : start ≥ -100) (h2 : start ≤ 100)
  (h3 : divisor > 0) (h4 : divisor ≤ 10) :
  find_divisible_numbers start (start - 1) divisor = (0, 0) :=
  sorry
-- </vc-theorems>