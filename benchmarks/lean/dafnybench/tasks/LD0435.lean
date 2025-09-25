-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def q (x : Nat) (y : Nat) : Nat :=
sorry

def strange : Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem q_spec (x y z : Nat) :
y - x > 2 →
x < z*z ∧ z*z < y :=
sorry

theorem strange_spec :
1 = 2 :=
sorry

theorem vc1 (n : Nat) :
n ≥ 0 → 0 = 0*0 ∧ 0 ≤ n :=
sorry

theorem vc2 (i n sqn x : Nat) :
i < n ∧ i + 1 ≤ n ∧ sqn = i * i →
sqn = sqn + x ∧ i = i + 1 ∧ x = 2 * i + 1 :=
sorry

theorem vc3 (i n sqn : Nat) :
¬(i < n) ∧ i ≤ n ∧ sqn = i * i →
sqn = n * n :=
sorry
-- </vc-theorems>