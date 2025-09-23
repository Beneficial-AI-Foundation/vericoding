-- <vc-preamble>
partial def suma_aux (V : Array Int) (n : Nat) : Int :=
if n == V.size then
0
else
V[n]! + suma_aux V (n + 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def suma_componentes (V : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem suma_aux_spec (V : Array Int) (n : Nat) :
0 ≤ n ∧ n ≤ V.size →
suma_aux V n = if n == V.size then 0 else V[n]! + suma_aux V (n + 1) :=
sorry

theorem suma_componentes_spec (V : Array Int) :
suma_componentes V = suma_aux V 0 :=
sorry
-- </vc-theorems>