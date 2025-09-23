-- <vc-preamble>
partial def Sum_ (a : Array Int) (s t : Int) : Int :=
if s = t then 0 else Sum_ a s (t-1) + a[(t-1).toNat]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MaxSegSum (a : Array Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Sum_spec (a : Array Int) (s t : Int) :
0 ≤ s ∧ s ≤ t ∧ t ≤ a.size → Sum_ a s t ≥ 0 :=
sorry

theorem MaxSegSum_spec (a : Array Int) :
let (k, m) := MaxSegSum a
0 ≤ k ∧ k ≤ m ∧ m ≤ a.size ∧
(∀ p q, 0 ≤ p ∧ p ≤ q ∧ q ≤ a.size → Sum_ a p q ≤ Sum_ a k m) :=
sorry
-- </vc-theorems>