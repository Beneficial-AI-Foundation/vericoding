-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def torneo (valores : Array Float) (i j k : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem torneo_spec (valores : Array Float) (i j k : Nat) :
(valores.size ≥ 20 ∧ valores.size < 50) →
(i ≥ 0 ∧ j ≥ 0 ∧ k ≥ 0) →
(i < valores.size ∧ j < valores.size ∧ k < valores.size) →
(i ≠ j ∧ j ≠ k ∧ k ≠ i) →
let (pos_padre, pos_madre) := torneo valores i j k
∃ p q r,
(p ∈ [i, j, k] ∧ q ∈ [i, j, k] ∧ r ∈ [i, j, k]) ∧
(p ≠ q ∧ q ≠ r ∧ p ≠ r) ∧
(valores[p]! ≥ valores[q]! ∧ valores[q]! ≥ valores[r]!) ∧
pos_padre = p ∧ pos_madre = q :=
sorry
-- </vc-theorems>