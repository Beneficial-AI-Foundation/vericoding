-- <vc-preamble>
/- Helper function to compute sum of a list recursively -/
def sumTo : List Int → Int
  | [] => 0  
  | xs => 
    if h : xs = [] then 0 
    else 
      have h_len : xs.length - 1 < xs.length := by
        have : xs.length > 0 := by
          cases xs with
          | nil => simp at h
          | cons _ _ => simp
        omega
      sumTo (xs.dropLast) + xs.getLast!
termination_by xs => xs.length

@[reducible, simp]
def sum_precond (arr : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Test cases and examples can be added here -/