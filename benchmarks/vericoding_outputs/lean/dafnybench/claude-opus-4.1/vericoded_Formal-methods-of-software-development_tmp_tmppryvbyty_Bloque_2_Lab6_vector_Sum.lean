import Mathlib
-- <vc-preamble>
partial def sum (v : Array Int) : Int :=
if v.size = 0 then 0
else if v.size = 1 then v[0]!
else v[0]! + sum (v.extract 1 v.size)

partial def scalar_product (v1 v2 : Array Int) : Int :=
if v1.size = 0 then 0
else v1[0]! * v2[0]! + scalar_product (v1.extract 1 v1.size) (v2.extract 1 v2.size)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed since we're just wrapping the existing sum function
-- </vc-helpers>

-- <vc-definitions>
def vector_Sum (v : Array Int) : Int :=
sum v
-- </vc-definitions>

-- <vc-theorems>
theorem scalar_product_spec (v1 v2 : Array Int) :
v1.size = v2.size → scalar_product v1 v2 = scalar_product v1 v2 :=
fun h => rfl

theorem vector_Sum_spec (v : Array Int) (x : Int) :
vector_Sum v = sum v :=
by
  -- vector_Sum is defined as sum v, so this is reflexive
  unfold vector_Sum
  rfl
-- </vc-theorems>
