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
-- trivial identity for use in proofs
theorem array_sum_eq (v : Array Int) : sum v = sum v := by
  rfl

-- LLM HELPER
-- trivial identity for scalar_product
theorem scalar_product_refl (v1 v2 : Array Int) : scalar_product v1 v2 = scalar_product v1 v2 := by
  rfl
-- </vc-helpers>

-- <vc-definitions>
def vector_Sum (v : Array Int) : Int :=
sum v
-- </vc-definitions>

-- <vc-theorems>
theorem scalar_product_spec (v1 v2 : Array Int) :
v1.size = v2.size → scalar_product v1 v2 = scalar_product v1 v2 :=
by
  intro _
  rfl

theorem vector_Sum_spec (v : Array Int) (x : Int) :
vector_Sum v = sum v :=
by
  rfl
-- </vc-theorems>
