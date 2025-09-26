-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lottery (s : String) : String := sorry

def dedup (list : List α) [BEq α] : List α := list.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
-- </vc-definitions>

-- <vc-theorems>
theorem lottery_result_format (s : String) : 
    let result := lottery s
    (result = "One more run!" ∨ result.all Char.isDigit) := by sorry

theorem lottery_preserves_digit_order (s : String) : 
    let result := lottery s
    result ≠ "One more run!" →
    let input_digits := s.toList.filter Char.isDigit
    result.toList = dedup input_digits := by sorry

theorem lottery_no_duplicates (s : String) :
    let result := lottery s  
    result ≠ "One more run!" →
    result.toList.length = (dedup result.toList).length := by sorry

theorem lottery_all_digits_input (s : String) :
    s.all Char.isDigit → s.length > 0 →
    let result := lottery s
    result.all Char.isDigit ∧ 
    result.toList.length = (dedup result.toList).length := by sorry
-- </vc-theorems>