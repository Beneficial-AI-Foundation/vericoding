-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAllSame (s : String) : Bool := sorry

def solveBinaryConversion (source target : String) : Bool × Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_same_string_impossible (s : String) (h : s.length > 0) :
  isAllSame s = true →
  let target := if s.contains '0' then String.mk (List.replicate s.length '1')
                else String.mk (List.replicate s.length '0')
  let result := solveBinaryConversion s target
  result.1 = false ∧ result.2 = 0 := sorry

theorem identical_strings_need_no_ops (s : String) (h : s.length > 0) :
  isAllSame s = false →
  let result := solveBinaryConversion s s
  result.1 = true ∧ result.2 = 0 := sorry

theorem result_is_maximal_differences (s : String) (h : s.length > 0) :
  isAllSame s = false →
  let target := String.mk (s.toList.map (fun c => if c = '0' then '1' else '0'))
  let zeros_to_ones := s.toList.filter (· = '0') |>.length
  let ones_to_zeros := s.toList.filter (· = '1') |>.length
  let result := solveBinaryConversion s target
  result.1 = true ∧ result.2 = max zeros_to_ones ones_to_zeros := sorry
-- </vc-theorems>