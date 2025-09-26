import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
@[simp]
theorem Vector.toList_map_id {n : Nat} {α : Type} (v : Vector α n) :
  (v.map id).toList = v.toList := by
  simp

-- LLM HELPER
@[simp]
theorem Vector.get_map_id {n : Nat} {α : Type} (v : Vector α n) (i : Fin n) :
  (v.map id)[i] = v[i] := by
  simp

-- </vc-helpers>

-- <vc-definitions>
def copy {n : Nat} (arr : Vector Int n) : Vector Int n :=
Vector.map id arr
-- </vc-definitions>

-- <vc-theorems>
theorem copy_spec {n : Nat} (arr : Vector Int n) :
  (copy arr).toList.length = n ∧
  ∀ i : Fin n, (copy arr)[i] = arr[i] :=
by
  simp [copy]
-- </vc-theorems>
