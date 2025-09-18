-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_exp (s : String) : List String := sorry

def stringToFloat (s : String) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_exp_sum_equals_original (s : String) :
  let result := split_exp s
  if result.isEmpty then 
    ∀ (c : Char), s.replace "." "" |>.data.contains c → c = '0'
  else
    let sum := result.foldl (fun acc x => acc + stringToFloat x) 0
    (stringToFloat s - sum).abs < 1e-10 := sorry

theorem split_exp_all_components_nonzero (s : String) :
  let result := split_exp s
  ∀ component, component ∈ result →
    (component.toList.filter (fun c => c.isDigit && c ≠ '0')).length = 1 := sorry

theorem split_exp_ordering (s : String) :
  let result := split_exp s
  let float_results := result.map stringToFloat
  ∀ i j, i < j → j < float_results.length → 
    float_results[i]! ≥ float_results[j]! := sorry

theorem split_exp_zero :
  split_exp "0" = [] ∧
  split_exp "0.0" = [] ∧
  split_exp "00.00" = [] := sorry
-- </vc-theorems>