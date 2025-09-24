-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_balance_point (arr : List Int) : Int := sorry 

def sum_list (arr : List Int) : Int := sorry

-- Valid index property
-- </vc-definitions>

-- <vc-theorems>
theorem balance_point_valid_index (arr : List Int) :
  let bp := find_balance_point arr
  bp ≠ -1 → 0 ≤ bp ∧ bp < arr.length := sorry

-- Equal sums property 

theorem balance_point_equal_sums (arr : List Int) :
  let bp := find_balance_point arr
  bp ≠ -1 → 
    (bp = 0 → sum_list (arr.drop 1) = 0) ∧
    (bp = arr.length - 1 → sum_list (arr.take (arr.length - 1)) = 0) ∧
    (0 < bp ∧ bp < arr.length - 1 → 
      sum_list (arr.take (Int.toNat bp)) = sum_list (arr.drop (Int.toNat (bp + 1)))) := sorry

-- Symmetry property

theorem balance_point_symmetry (arr : List Int) :
  let bp1 := find_balance_point arr
  let bp2 := find_balance_point arr.reverse
  bp1 = -1 ↔ bp2 = -1 ∧
  bp1 ≠ -1 → bp1 + bp2 = arr.length - 1 := sorry

-- Single element property  

theorem balance_point_single_elem (x : Int) :
  find_balance_point [x] = 0 := sorry

-- No balance preservation property

theorem no_balance_preserves (arr : List Int) :
  find_balance_point arr = -1 →
  find_balance_point (arr.map (· * 2)) = -1 := sorry
-- </vc-theorems>