-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def matchFn (usefulness : List Nat) (months : Nat) : String := sorry

theorem match_result (usefulness : List Nat) (months : Nat) : 
  matchFn usefulness months = "Match!" ∨ matchFn usefulness months = "No match!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem match_monotone_usefulness (usefulness : List Nat) (months : Nat) :
  matchFn usefulness months = "Match!" →
  matchFn (usefulness.map (fun x => if x > 0 then x - 1 else 0)) months = "Match!" := sorry

theorem match_monotone_months (usefulness : List Nat) (months : Nat) :
  matchFn usefulness months = "No match!" →
  matchFn usefulness (months + 1) = "No match!" := sorry

theorem match_zero_usefulness (usefulness : List Nat) (months : Nat) :
  matchFn (List.replicate usefulness.length 0) months = "No match!" := sorry

theorem match_max_usefulness (usefulness : List Nat) :
  matchFn (List.replicate usefulness.length 100) 0 = "Match!" := sorry
-- </vc-theorems>