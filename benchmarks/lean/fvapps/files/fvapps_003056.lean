-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reducePyramid (base : List Int) : Int :=
  sorry

def referencePyramidReduce (base : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matches_reference_implementation {base : List Int}
  (h : base.length > 0 ∧ base.length ≤ 10) :
  reducePyramid base = referencePyramidReduce base :=
sorry

theorem single_element {base : List Int}
  (h : base.length = 1) :
  reducePyramid base = base.get ⟨0, sorry⟩ :=
sorry

theorem two_elements {base : List Int}
  (h : base.length = 2) :
  reducePyramid base = base.get ⟨0, sorry⟩ + base.get ⟨1, sorry⟩ :=
sorry

theorem singleton_list (x : Int) :
  reducePyramid [x] = x :=
sorry
-- </vc-theorems>