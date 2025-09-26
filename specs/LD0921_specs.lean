-- <vc-preamble>
def sum (X_val : Array Int) (X_crd : Array Nat) (v : Array Int) (b : Nat) (k : Nat) : Int :=
if k ≤ b then
0
else
sum X_val X_crd v (b + 1) k + X_val[b]! * v[X_crd[b]!]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SpMV (X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat) (v : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (X_val : Array Int) (X_crd : Array Nat) (v : Array Int) (b k : Nat) :
X_val.size ≥ b ∧ b ≥ 0 ∧
k ≤ X_val.size ∧
X_val.size = X_crd.size ∧
(∀ i, 0 ≤ i ∧ i < X_crd.size → X_crd[i]! < v.size) →
sum X_val X_crd v b k ≥ 0 :=
sorry

theorem SpMV_spec (X_val : Array Int) (X_crd : Array Nat) (X_pos : Array Nat) (v : Array Int) :
X_crd.size ≥ 1 ∧
X_crd.size = X_val.size ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < X_pos.size → X_pos[i]! ≤ X_pos[j]!) ∧
(∀ i, 0 ≤ i ∧ i < X_crd.size → X_crd[i]! < v.size) ∧
(∀ i, 0 ≤ i ∧ i < X_pos.size → X_pos[i]! ≤ X_val.size) ∧
X_pos.size ≥ 1 →
let y := SpMV X_val X_crd X_pos v
y.size + 1 = X_pos.size ∧
(∀ i, 0 ≤ i ∧ i < y.size → y[i]! = sum X_val X_crd v (X_pos[i]!) (X_pos[i + 1]!)) :=
sorry
-- </vc-theorems>