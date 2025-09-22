-- <vc-preamble>
partial def power (a : Int) (n : Int) : Int :=
if n == 0 then 1 else a * power a (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def A8Q1 (y0 : Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem A8Q1_spec (y0 : Int) (x : Int) :
y0 ≥ 0 → A8Q1 y0 x = power x y0 :=
sorry
-- </vc-theorems>