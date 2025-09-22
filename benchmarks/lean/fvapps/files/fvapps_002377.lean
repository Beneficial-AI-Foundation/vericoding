-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum_product (nums : List Int) : Int := sorry

theorem maximum_product_scales {nums : List Int} (h : nums.length ≥ 3) (scale : Int) (h2 : scale > 0) :
  maximum_product (nums.map (· * scale)) = maximum_product nums * (scale * scale * scale) := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>