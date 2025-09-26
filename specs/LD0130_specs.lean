-- <vc-preamble>
partial def min (v : Array Int) (i : Nat) : Int :=
if i = 1 then v[0]!
else if v[i-1]! ≤ min v (i-1) then v[i-1]!
else min v (i-1)

partial def countMin (v : Array Int) (x : Int) (i : Nat) : Int :=
if i = 0 then 0
else if v[i-1]! = x then 1 + countMin v x (i-1)
else countMin v x (i-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mCountMin (v : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_spec (v : Array Int) (i : Nat) :
1 ≤ i ∧ i ≤ v.size →
∀ k, 0 ≤ k ∧ k < i → v[k]! ≥ min v i :=
sorry

theorem countMin_spec (v : Array Int) (x : Int) (i : Nat) :
0 ≤ i ∧ i ≤ v.size →
countMin v x i = 0 :=
sorry

theorem mCountMin_spec (v : Array Int) :
v.size > 0 →
mCountMin v = countMin v (min v v.size) v.size :=
sorry
-- </vc-theorems>