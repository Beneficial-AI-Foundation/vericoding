

/-!
{
"name": "vfag_tmp_tmpc29dxm1j_Verificacion_torneo_torneo",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: vfag_tmp_tmpc29dxm1j_Verificacion_torneo_torneo",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translates the Dafny torneo method which takes an array of reals and three indices
and returns positions of two highest values.

@param valores Array of real numbers
@param i First index
@param j Second index
@param k Third index
@return Tuple of (pos_padre, pos_madre) containing indices of two highest values
-/
def torneo (valores : Array Float) (i j k : Int) : Int × Int := sorry

/--
Specification for torneo method ensuring:
1. Array is non-null and has valid length
2. Indices are valid and distinct
3. Returns indices of two highest values among the three positions
-/
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
pos_padre = p ∧ pos_madre = q := sorry
