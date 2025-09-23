-- <vc-preamble>
partial def has_count (v : Int) (a : Array Int) (n : Int) : Int :=
if n == 0 then 0
else if a[(n-1).toNat]! == v
then has_count v a (n-1) + 1
else has_count v a (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count (v : Int) (a : Array Int) (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_spec (v : Int) (a : Array Int) (n : Int) :
n ≥ 0 ∧ n ≤ a.size →
count v a n = has_count v a n :=
sorry
-- </vc-theorems>