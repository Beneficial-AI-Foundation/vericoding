-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dominator (arr : List Int) : Int := sorry

theorem dominator_empty_list :
  dominator [] = -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dominator_singleton (x : Int) :
  dominator [x] = x := sorry

theorem dominator_majority {base : List Int} {dom_value : Int} {repeats : Nat}
  (h_repeats : repeats > base.length) :
  dominator (base ++ List.replicate repeats dom_value) = dom_value := sorry
-- </vc-theorems>