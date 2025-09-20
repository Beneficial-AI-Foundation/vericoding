-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def first_tooth (lst : List Int) : Int := sorry

theorem first_tooth_output_range {lst : List Int} (h : lst.length ≥ 2) :
  let result := first_tooth lst
  result = -1 ∨ (0 ≤ result ∧ result < lst.length) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem constant_list_gives_negative_one {lst : List Int} (h : lst.length ≥ 2) :
  let val := lst.get ⟨0, sorry⟩
  let constant_list := List.replicate lst.length val
  first_tooth constant_list = -1 := sorry
-- </vc-theorems>