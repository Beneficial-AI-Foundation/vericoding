import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Projections for readability -/
def pair_more (p : Int × Int) : Int := p.1
def pair_less (p : Int × Int) : Int := p.2

-- </vc-helpers>

-- <vc-definitions>
def MultipleReturns (x y : Int) : Int × Int :=
(x + y, x - y)
-- </vc-definitions>

-- <vc-theorems>
theorem MultipleReturns_spec (x y : Int) :
let (more, less) := MultipleReturns x y
more = x + y ∧ less = x - y :=
by
  -- unfolding MultipleReturns replaces the let-bound pair with (x + y, x - y)
  simp [MultipleReturns]
-- </vc-theorems>
