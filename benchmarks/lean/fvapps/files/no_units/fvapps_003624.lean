-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_mixed_num (frac: String) : String := sorry

def is_valid_mixed_num (result: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mixed_num_is_valid {n d: Nat} (h1: 0 < n) (h2: n ≤ 10000) (h3: 0 < d) (h4: d ≤ 100) :
  is_valid_mixed_num (get_mixed_num s!"{n}/{d}") := sorry

theorem mixed_num_components_sum {n d: Nat} (h1: 0 < n) (h2: n ≤ 10000) (h3: 0 < d) (h4: d ≤ 100) :
  let result := get_mixed_num s!"{n}/{d}"
  let whole := result.splitOn " " |>.head!
  let frac := result.splitOn " " |>.tail!.head!
  let n2 := frac.splitOn "/" |>.head!
  let d2 := frac.splitOn "/" |>.tail!.head!
  (whole.toNat! * d2.toNat! + n2.toNat! = n) ∧ (d2.toNat! = d) := sorry

theorem whole_numbers {n: Nat} (h: 0 < n) (h2: n ≤ 100) :
  get_mixed_num s!"{n}/1" = s!"{n} 0/1" := sorry

theorem edge_cases :
  (get_mixed_num "1/1" = "1 0/1") ∧ 
  (get_mixed_num "0/1" = "0 0/1") := sorry
-- </vc-theorems>